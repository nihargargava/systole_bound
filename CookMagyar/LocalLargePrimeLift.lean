module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalNonsingular
public import CookMagyar.LocalCount
public import Mathlib.Data.ZMod.Units

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # One-step lifting at primes at least five

This file develops the exact finite algebra needed to lift unit solutions
of the diagonal equation `Σ (x³-x) = T` from `p^k` to `p^(k+1)`.
-/

/-- Core.Reduction from level `k+1` to level `k`. -/
def primePowerReduction (p k : ℕ) :
    ZMod (p ^ (k + 1)) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))

/-- Embed the standard representative of a residue modulo `p` into the
next prime-power residue ring.  This is not a ring homomorphism, but after
multiplication by `p^k` it parametrizes the kernel of reduction. -/
def primePowerDigit (p k : ℕ) [NeZero p] (a : ZMod p) :
    ZMod (p ^ (k + 1)) := a.val

/-- Exact Taylor identity for the cubic `X³-X`. -/
theorem cubicResidue_add_taylor {q : ℕ} (x h : ZMod q) :
    cubicResidue (x + h) =
      cubicResidue x + h * cubicDerivative x +
        h ^ 2 * (3 * x + h) := by
  simp only [cubicResidue, cubicDerivative]
  ring

/-- At level `p^(k+1)`, the square of `p^k` vanishes when `k ≥ 1`. -/
theorem primePower_step_square_zero (p k : ℕ) (hk : 1 ≤ k) :
    ((p ^ k : ZMod (p ^ (k + 1))) ^ 2) = 0 := by
  have hdiv : p ^ (k + 1) ∣ (p ^ k) ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  have hz : (((p ^ k) ^ 2 : ℕ) : ZMod (p ^ (k + 1))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simpa using hz

/-- Taylor linearization is exact for a one-digit correction modulo the
next prime power. -/
theorem cubicResidue_add_primePower_mul (p k : ℕ) (hk : 1 ≤ k)
    (x y : ZMod (p ^ (k + 1))) :
    cubicResidue (x + (p ^ k : ZMod (p ^ (k + 1))) * y) =
      cubicResidue x +
        (p ^ k : ZMod (p ^ (k + 1))) * y * cubicDerivative x := by
  rw [cubicResidue_add_taylor]
  have hsquare := primePower_step_square_zero p k hk
  have hcorrection : ((p ^ k : ZMod (p ^ (k + 1))) * y) ^ 2 = 0 := by
    rw [mul_pow, hsquare, zero_mul]
  rw [hcorrection, zero_mul, add_zero]

/-- A one-digit correction does not alter reduction to the preceding
prime-power level. -/
theorem primePowerReduction_add_digit (p k : ℕ) [NeZero p]
    (x : ZMod (p ^ (k + 1))) (a : ZMod p) :
    primePowerReduction p k (x + p ^ k * primePowerDigit p k a) =
      primePowerReduction p k x := by
  rw [map_add, map_mul]
  have hz : primePowerReduction p k
      (p ^ k : ZMod (p ^ (k + 1))) = 0 := by
    rw [map_pow, map_natCast]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul, add_zero]

/-- More generally, every multiple of `p^k` disappears on reduction to
level `k`. -/
theorem primePowerReduction_add_primePower_mul (p k : ℕ) [NeZero p]
    (x y : ZMod (p ^ (k + 1))) :
    primePowerReduction p k
        (x + (p ^ k : ZMod (p ^ (k + 1))) * y) =
      primePowerReduction p k x := by
  rw [map_add, map_mul]
  have hz : primePowerReduction p k
      (p ^ k : ZMod (p ^ (k + 1))) = 0 := by
    rw [map_pow, map_natCast]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul, add_zero]

/-- Multiplication by `p^k` makes equality modulo `p` into equality modulo
`p^(k+1)`. -/
theorem primePower_mul_eq_of_cast_eq (p k : ℕ) [NeZero p]
    {a b : ZMod (p ^ (k + 1))}
    (h : (a.cast : ZMod p) = (b.cast : ZMod p)) :
    (p ^ k : ZMod (p ^ (k + 1))) * a = p ^ k * b := by
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
  simp only [← Nat.cast_pow, ← Nat.cast_mul]
  rw [ZMod.natCast_eq_natCast_iff]
  have hval : (a.val : ZMod p) = (b.val : ZMod p) := by
    simpa only [ZMod.cast_eq_val] using h
  have hmod : a.val ≡ b.val [MOD p] :=
    (ZMod.natCast_eq_natCast_iff a.val b.val p).mp hval
  have hmul := hmod.mul_left' (p ^ k)
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Every element killed by reduction from `p^(k+1)` to `p^k` is a
one-digit multiple of `p^k`. -/
theorem exists_primePowerDigit_of_reduction_eq_zero (p k : ℕ) [NeZero p]
    (e : ZMod (p ^ (k + 1))) (he : primePowerReduction p k e = 0) :
    ∃ a : ZMod p,
      e = (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k a := by
  have heval : (e.val : ZMod (p ^ k)) = 0 := by
    simpa only [primePowerReduction, ZMod.castHom_apply, ZMod.cast_eq_val] using he
  have hdiv : p ^ k ∣ e.val :=
    (ZMod.natCast_eq_zero_iff e.val (p ^ k)).mp heval
  rcases hdiv with ⟨a, ha⟩
  have hpkpos : 0 < p ^ k := pow_pos (NeZero.pos p) k
  have hval : e.val < p ^ k * p := by
    simpa [pow_succ] using e.val_lt
  have ha_lt : a < p := by
    apply (Nat.mul_lt_mul_left hpkpos).mp
    simpa [ha] using hval
  refine ⟨(a : ZMod p), ?_⟩
  rw [← ZMod.natCast_zmod_val e]
  simp [primePowerDigit, ZMod.val_natCast_of_lt ha_lt, ha]

/-- Distinct digits give distinct kernel elements. -/
theorem primePowerDigit_mul_injective (p k : ℕ) [NeZero p] :
    Function.Injective (fun a : ZMod p ↦
      (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k a) := by
  intro a b hab
  have hmod : p ^ k * a.val ≡ p ^ k * b.val [MOD p ^ (k + 1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    unfold primePowerDigit at hab
    simpa only [Nat.cast_mul, Nat.cast_pow] using hab
  have hpkpos : 0 < p ^ k := pow_pos (NeZero.pos p) k
  have ha_lt : p ^ k * a.val < p ^ (k + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_left a.val_lt hpkpos
  have hb_lt : p ^ k * b.val < p ^ (k + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_left b.val_lt hpkpos
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
  have habval : a.val = b.val := Nat.eq_of_mul_eq_mul_left hpkpos hmod
  exact ZMod.val_injective p habval

/-- The kernel of one-step reduction is exactly the `p` possible digits. -/
noncomputable def primePowerKernelEquiv (p k : ℕ) [NeZero p] :
    ZMod p ≃ {e : ZMod (p ^ (k + 1)) // primePowerReduction p k e = 0} := by
  let f : ZMod p →
      {e : ZMod (p ^ (k + 1)) // primePowerReduction p k e = 0} := fun a ↦
    ⟨(p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k a, by
      simpa using primePowerReduction_add_digit p k
        (0 : ZMod (p ^ (k + 1))) a⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply primePowerDigit_mul_injective p k
    exact congrArg Subtype.val hab
  · rintro ⟨e, he⟩
    rcases exists_primePowerDigit_of_reduction_eq_zero p k e he with ⟨a, ha⟩
    refine ⟨a, Subtype.ext ?_⟩
    exact ha.symm

/-- Consequently, the one-step reduction kernel has exactly `p` elements. -/
theorem card_primePowerReduction_kernel (p k : ℕ) [NeZero p] :
    Fintype.card
      {e : ZMod (p ^ (k + 1)) // primePowerReduction p k e = 0} = p := by
  calc
    Fintype.card
        {e : ZMod (p ^ (k + 1)) // primePowerReduction p k e = 0} =
        Fintype.card (ZMod p) :=
      (Fintype.card_congr (primePowerKernelEquiv p k)).symm
    _ = p := ZMod.card p

/-- A residue at level `k+1` is a unit whenever its reduction to level `k`
is a unit.  The proof writes its difference from a lifted unit as a
square-zero one-digit correction. -/
theorem isUnit_of_primePowerReduction_isUnit (p k : ℕ) [NeZero p]
    (hk : 1 ≤ k) (x : ZMod (p ^ (k + 1)))
    (hx : IsUnit (primePowerReduction p k x)) : IsUnit x := by
  let hpow : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hpow hx.unit
  have hured : primePowerReduction p k (u : ZMod (p ^ (k + 1))) =
      primePowerReduction p k x := by
    have huval := congrArg (fun v : (ZMod (p ^ k))ˣ ↦ (v : ZMod (p ^ k))) hu
    simpa [primePowerReduction, ZMod.unitsMap_val, IsUnit.unit_spec] using huval
  let e : ZMod (p ^ (k + 1)) := x - u
  have hered : primePowerReduction p k e = 0 := by
    simp [e, map_sub, hured]
  rcases exists_primePowerDigit_of_reduction_eq_zero p k e hered with ⟨a, ha⟩
  have he_square : e ^ 2 = 0 := by
    rw [ha, mul_pow, primePower_step_square_zero p k hk, zero_mul]
  have he_nilpotent : IsNilpotent e := ⟨2, he_square⟩
  have hx_eq : x = (u : ZMod (p ^ (k + 1))) + e := by
    simp [e]
  rw [hx_eq]
  exact he_nilpotent.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)

/-- One-step multivariable Hensel lifting for the diagonal cubic.  A
distinguished unit partial derivative makes the single linear correction
solvable, while all coordinates remain units. -/
theorem nonsingularUnitSolution_lift_step {p k n : ℕ} [NeZero p]
    (hp : p.Prime) (hk : 1 ≤ k) {t : ZMod (p ^ k)}
    (s : NonsingularUnitSolution (p ^ k) n t) (j : Fin n)
    (hj : IsUnit (cubicDerivative (s.point j)))
    (T : ZMod (p ^ (k + 1))) (hT : primePowerReduction p k T = t) :
    ∃ lifted : NonsingularUnitSolution (p ^ (k + 1)) n T,
      (∀ i, primePowerReduction p k (lifted.point i) = s.point i) ∧
        IsUnit (cubicDerivative (lifted.point j)) := by
  classical
  let hpow : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)
  let baseUnit : Fin n → (ZMod (p ^ k))ˣ :=
    fun i ↦ (s.isUnit_point i).unit
  let liftedUnit : Fin n → (ZMod (p ^ (k + 1)))ˣ := fun i ↦
    Classical.choose (ZMod.unitsMap_surjective hpow (baseUnit i))
  have liftedUnit_spec (i : Fin n) :
      ZMod.unitsMap hpow (liftedUnit i) = baseUnit i :=
    Classical.choose_spec (ZMod.unitsMap_surjective hpow (baseUnit i))
  let x : Fin n → ZMod (p ^ (k + 1)) := fun i ↦ liftedUnit i
  have hx_unit (i : Fin n) : IsUnit (x i) := (liftedUnit i).isUnit
  have hx_red (i : Fin n) : primePowerReduction p k (x i) = s.point i := by
    have hval := congrArg (fun u : (ZMod (p ^ k))ˣ ↦ (u : ZMod (p ^ k)))
      (liftedUnit_spec i)
    simpa [x, baseUnit, primePowerReduction, ZMod.unitsMap_val,
      IsUnit.unit_spec] using hval
  have hcubic_red (i : Fin n) :
      primePowerReduction p k (cubicResidue (x i)) =
        cubicResidue (s.point i) := by
    simp only [cubicResidue, map_sub, map_pow, hx_red]
  have hsum_red :
      primePowerReduction p k (∑ i, cubicResidue (x i)) = t := by
    rw [map_sum]
    simp_rw [hcubic_red]
    exact s.equation
  let e : ZMod (p ^ (k + 1)) := T - ∑ i, cubicResidue (x i)
  have he_red : primePowerReduction p k e = 0 := by
    simp [e, map_sub, hT, hsum_red]
  rcases exists_primePowerDigit_of_reduction_eq_zero p k e he_red with ⟨a, ha⟩
  have hderivative_red :
      primePowerReduction p k (cubicDerivative (x j)) =
        cubicDerivative (s.point j) := by
    have hthree : primePowerReduction p k
        (3 : ZMod (p ^ (k + 1))) = (3 : ZMod (p ^ k)) :=
      map_ofNat (primePowerReduction p k) 3
    unfold cubicDerivative
    rw [map_sub, map_mul, map_pow, hx_red, hthree, map_one]
  have hd_unit : IsUnit (cubicDerivative (x j)) := by
    apply isUnit_of_primePowerReduction_isUnit p k hk
    simpa [hderivative_red] using hj
  let d : ZMod (p ^ (k + 1)) := cubicDerivative (x j)
  let c : ZMod (p ^ (k + 1)) := primePowerDigit p k a * d⁻¹
  let corrected : ZMod (p ^ (k + 1)) :=
    x j + (p ^ k : ZMod (p ^ (k + 1))) * c
  have hcorrected_cubic :
      cubicResidue corrected = cubicResidue (x j) + e := by
    rw [show corrected = x j +
      (p ^ k : ZMod (p ^ (k + 1))) * c from rfl]
    rw [cubicResidue_add_primePower_mul p k hk]
    congr 1
    calc
      (p ^ k : ZMod (p ^ (k + 1))) * c * cubicDerivative (x j) =
          (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k a := by
        simp only [c, d]
        rw [mul_assoc, mul_assoc (primePowerDigit p k a),
          ZMod.inv_mul_of_unit _ hd_unit, mul_one]
      _ = e := ha.symm
  let point : Fin n → ZMod (p ^ (k + 1)) := Function.update x j corrected
  have hpoint_red (i : Fin n) :
      primePowerReduction p k (point i) = s.point i := by
    by_cases hij : i = j
    · subst i
      simp [point, corrected, primePowerReduction_add_primePower_mul, hx_red]
    · simp [point, hij, hx_red]
  have hpoint_unit (i : Fin n) : IsUnit (point i) := by
    apply isUnit_of_primePowerReduction_isUnit p k hk
    rw [hpoint_red]
    exact s.isUnit_point i
  have hpoint_derivative_red :
      primePowerReduction p k (cubicDerivative (point j)) =
        cubicDerivative (s.point j) := by
    have hthree : primePowerReduction p k
        (3 : ZMod (p ^ (k + 1))) = (3 : ZMod (p ^ k)) :=
      map_ofNat (primePowerReduction p k) 3
    unfold cubicDerivative
    rw [map_sub, map_mul, map_pow, hpoint_red, hthree, map_one]
  have hpoint_derivative_unit : IsUnit (cubicDerivative (point j)) := by
    apply isUnit_of_primePowerReduction_isUnit p k hk
    simpa [hpoint_derivative_red] using hj
  have hpoint_equation : ∑ i, cubicResidue (point i) = T := by
    calc
      (∑ i, cubicResidue (point i)) =
          (∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
            cubicResidue (point i)) + cubicResidue (point j) :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ = (∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
            cubicResidue (x i)) + cubicResidue corrected := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          simp [point, hij]
        · simp [point]
      _ = (∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
            cubicResidue (x i)) + (cubicResidue (x j) + e) := by
        rw [hcorrected_cubic]
      _ = (∑ i, cubicResidue (x i)) + e := by
        rw [← add_assoc, Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      _ = T := by
        simp [e]
  letI : Fact (1 < p ^ (k + 1)) :=
    ⟨one_lt_pow₀ hp.one_lt (by omega)⟩
  let lifted : NonsingularUnitSolution (p ^ (k + 1)) n T := {
    point := point
    isUnit_point := hpoint_unit
    equation := hpoint_equation
    nonsingular := ⟨j, hpoint_derivative_unit.ne_zero⟩
  }
  exact ⟨lifted, hpoint_red, hpoint_derivative_unit⟩

/-- Nonsingular unit solutions exist at every positive prime-power level.
The same distinguished partial derivative remains a unit throughout the
induction. -/
theorem nonsingularUnitSolution_primePower_exists {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (T k : ℕ) (hk : 1 ≤ k) :
    ∃ s : NonsingularUnitSolution (p ^ k) n (T : ZMod (p ^ k)),
      ∃ j : Fin n, IsUnit (cubicDerivative (s.point j)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  induction k, hk using Nat.le_induction with
  | base =>
      rw [Nat.pow_one]
      letI : Fact p.Prime := ⟨hp⟩
      rcases nonsingularUnitSolution_exists hp hp5 hn5 (T : ZMod p) with ⟨s⟩
      rcases s.nonsingular with ⟨j, hj⟩
      exact
        (show ∃ s : NonsingularUnitSolution p n (T : ZMod p),
            ∃ j : Fin n, IsUnit (cubicDerivative (s.point j)) from
          ⟨s, j, isUnit_iff_ne_zero.mpr hj⟩)
  | succ k hk ih =>
      rcases ih with ⟨s, j, hj⟩
      have htarget : primePowerReduction p k
          (T : ZMod (p ^ (k + 1))) = (T : ZMod (p ^ k)) := by
        exact map_natCast (primePowerReduction p k) T
      rcases nonsingularUnitSolution_lift_step hp hk s j hj
          (T : ZMod (p ^ (k + 1))) htarget with ⟨lifted, _hred, hderivative⟩
      exact ⟨lifted, j, hderivative⟩

/-- In particular, every positive prime-power-level unit count is positive
for primes at least five and at least five variables. -/
theorem unitCubicSolutionCount_primePower_pos {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (T k : ℕ) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    0 < CookMagyarFiniteFourier.unitCubicSolutionCount n
      (T : ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases nonsingularUnitSolution_primePower_exists hp hp5 hn5 T k hk with
    ⟨s, _j, _hderivative⟩
  exact CookMagyarFiniteFourier.unitCubicSolutionCount_pos_of_nonsingular s

/-- Every finite-level normalized local count is strictly positive at a
large prime. -/
theorem normalizedUnitCubicCount_primePower_pos {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (T k : ℕ) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    0 < CookMagyarFiniteFourier.normalizedUnitCubicCount n
      (T : ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply CookMagyarFiniteFourier.normalizedUnitCubicCount_pos
  · exact one_lt_pow₀ hp.one_lt (by omega)
  · exact unitCubicSolutionCount_primePower_pos hp hp5 hn5 T k hk

/-- An explicit finite-level lower bound obtained from the constructed
solution.  The stronger `p^(n-1)` lift multiplicity would make this bound
uniform in `k`; this theorem records the unconditional bound supplied by
one nonsingular lifted solution at every level. -/
theorem normalizedUnitCubicCount_primePower_lower_bound {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (T k : ℕ) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    (p ^ k : ℝ) / (Nat.totient (p ^ k) : ℝ) ^ n ≤
      CookMagyarFiniteFourier.normalizedUnitCubicCount n
        (T : ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcount : 0 < CookMagyarFiniteFourier.unitCubicSolutionCount n
      (T : ZMod (p ^ k)) :=
    unitCubicSolutionCount_primePower_pos hp hp5 hn5 T k hk
  have hcount_real : (1 : ℝ) ≤
      CookMagyarFiniteFourier.unitCubicSolutionCount n
        (T : ZMod (p ^ k)) := by
    exact_mod_cast hcount
  have htotient : 0 < (Nat.totient (p ^ k) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have hdenominator : 0 < (Nat.totient (p ^ k) : ℝ) ^ n :=
    pow_pos htotient n
  unfold CookMagyarFiniteFourier.normalizedUnitCubicCount
  apply (div_le_div_iff_of_pos_right hdenominator).2
  have hmodulus : 0 ≤ (p ^ k : ℝ) := by positivity
  simpa using mul_le_mul_of_nonneg_left hcount_real hmodulus

end CookMagyarLocal
end SystolicGrowth
