module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaMoment
public import CookMagyar.HuaDivisorBound
public import CookMagyar.PrimePowerAsymptotic

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped ArithmeticFunction BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # An unconditional elementary bound for the cubic eighth moment

`HuaMoment` identifies the weighted eighth moment exactly with an additive
energy.  Here we remove the von--Mangoldt weights, prove a finite fiber
bound for `x ↦ x³-x`, and obtain an unconditional polynomial upper bound.

The elementary solution-count bound has exponent `7`. The divisor-fiber
argument below improves it to `6+ε`. This module now also proves the
second-difference energy bound needed for the `5+ε` eighth moment;
the shift inequalities and final differencing assembly remain open.
-/

/-- The unweighted number of pairs of four-tuples with equal cubic sum. -/
def cubicEighthSolutionCount (N : ℕ) : ℕ :=
  ∑ x : Fin 4 → Fin (N + 1), ∑ y : Fin 4 → Fin (N + 1),
    if cubicFourTupleValue x = cubicFourTupleValue y then 1 else 0

/-- The natural cubic phase `x³ - x`, viewed in the integers, is the usual
monic cubic polynomial. -/
theorem primeCubic_cast_int (x : ℕ) :
    (primeCubic x : ℤ) = (x : ℤ) ^ 3 - x := by
  by_cases hx : x = 0
  · subst x
    simp [primeCubic]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have hle : x ≤ x ^ 3 := Nat.le_pow (by norm_num)
    simp [primeCubic, Nat.cast_sub hle]

/-- Factoring the difference of two cubic phases isolates the linear divisor
that begins the classical divisor-counting step in Hua's estimate. -/
theorem primeCubic_sub_factorization (a b : ℕ) :
    (primeCubic a : ℤ) - primeCubic b =
      ((a : ℤ) - b) *
        ((a : ℤ) ^ 2 + (a : ℤ) * b + (b : ℤ) ^ 2 - 1) := by
  rw [primeCubic_cast_int, primeCubic_cast_int]
  ring

/-- Any integer represented as a difference of cubic phases is divisible by
the difference of the underlying variables. -/
theorem variable_difference_dvd_primeCubic_difference
    (a b : ℕ) : ((a : ℤ) - b) ∣ (primeCubic a : ℤ) - primeCubic b := by
  rw [primeCubic_sub_factorization]
  exact dvd_mul_right _ _

/-- With a positive fixed difference `a-b`, the value of the cubic-phase
difference determines the pair `(a,b)`. This is the uniqueness step after
choosing the divisor `a-b` in the classical Hua divisor argument. -/
theorem primeCubic_difference_injective_of_same_positive_gap
    {a b c d : ℕ} (hab : b ≤ a) (hcd : d ≤ c)
    (hgap : 0 < a - b) (hgap_eq : a - b = c - d)
    (hvalue : (primeCubic a : ℤ) - primeCubic b =
      (primeCubic c : ℤ) - primeCubic d) : a = c ∧ b = d := by
  have hgapZ : (a : ℤ) - b = (c : ℤ) - d := by
    rw [← Nat.cast_sub hab, ← Nat.cast_sub hcd]
    exact_mod_cast hgap_eq
  let g : ℤ := (a : ℤ) - b
  have hgpos : 0 < g := by
    dsimp [g]
    rw [← Nat.cast_sub hab]
    exact_mod_cast hgap
  have ha : (a : ℤ) = b + g := by dsimp [g]; ring
  have hc : (c : ℤ) = d + g := by dsimp [g]; linarith
  rw [primeCubic_sub_factorization, primeCubic_sub_factorization] at hvalue
  have hq :
      (a : ℤ) ^ 2 + a * b + (b : ℤ) ^ 2 - 1 =
        (c : ℤ) ^ 2 + c * d + (d : ℤ) ^ 2 - 1 := by
    apply mul_left_cancel₀ hgpos.ne'
    simpa [g, hgapZ] using hvalue
  have hqa :
      (a : ℤ) ^ 2 + a * b + (b : ℤ) ^ 2 - 1 =
        3 * (b : ℤ) ^ 2 + 3 * b * g + g ^ 2 - 1 := by
    rw [ha]
    ring
  have hqc :
      (c : ℤ) ^ 2 + c * d + (d : ℤ) ^ 2 - 1 =
        3 * (d : ℤ) ^ 2 + 3 * d * g + g ^ 2 - 1 := by
    rw [hc]
    ring
  have hb_nonneg : (0 : ℤ) ≤ b := by positivity
  have hd_nonneg : (0 : ℤ) ≤ d := by positivity
  rcases lt_trichotomy b d with hbd | hbd | hbd
  · have hbdZ : (0 : ℤ) < (d : ℤ) - b :=
      sub_pos.mpr (by exact_mod_cast hbd)
    have hsum : (0 : ℤ) < (d : ℤ) + b + g := by linarith
    have hprod := mul_pos hbdZ hsum
    rw [hqa, hqc] at hq
    nlinarith [hprod]
  · have hacast : (a : ℤ) = c := by linarith [hgapZ]
    exact ⟨by exact_mod_cast hacast, hbd⟩
  · have hdbZ : (0 : ℤ) < (b : ℤ) - d :=
      sub_pos.mpr (by exact_mod_cast hbd)
    have hsum : (0 : ℤ) < (b : ℤ) + d + g := by linarith
    have hprod := mul_pos hdbZ hsum
    rw [hqa, hqc] at hq
    nlinarith [hprod]

/-- Ordered pairs in the finite summation interval with a fixed positive
phase difference. -/
def positiveCubicDifferencePairs (N m : ℕ) : Finset
    (Fin (N + 1) × Fin (N + 1)) :=
  (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).filter fun ab =>
    ab.2.val < ab.1.val ∧
      (primeCubic ab.1.val : ℤ) - primeCubic ab.2.val = (m : ℤ)

/-- A fixed positive cubic-phase difference has at most `τ(m)` ordered
representations with the first variable larger than the second. The map to
the positive gap is injective, and the factorization lemma puts each gap in
the divisor set of `m`. -/
theorem card_positiveCubicDifferencePairs_le_divisors
    (N m : ℕ) (hm : 0 < m) :
    (positiveCubicDifferencePairs N m).card ≤ m.divisors.card := by
  let gap : (Fin (N + 1) × Fin (N + 1)) → ℕ := fun ab =>
    ab.1.val - ab.2.val
  refine Finset.card_le_card_of_injOn gap ?_ ?_
  · intro ab hab
    rw [Finset.mem_coe]
    have hab' := (Finset.mem_filter.mp hab).2
    have hcast : ((gap ab : ℕ) : ℤ) =
        (ab.1.val : ℤ) - ab.2.val := by
      dsimp [gap]
      rw [Nat.cast_sub (Nat.le_of_lt hab'.1)]
    have hdivZ : ((ab.1.val : ℤ) - ab.2.val) ∣ (m : ℤ) := by
      rw [← hab'.2]
      exact variable_difference_dvd_primeCubic_difference ab.1.val ab.2.val
    have hdiv : gap ab ∣ m := by
      apply Int.natCast_dvd_natCast.mp
      simpa [hcast] using hdivZ
    exact Nat.mem_divisors.mpr ⟨hdiv, hm.ne'⟩
  · intro ab hab cd hcd hgap
    have hab' := (Finset.mem_filter.mp hab).2
    have hcd' := (Finset.mem_filter.mp hcd).2
    have hgap_eq : ab.1.val - ab.2.val = cd.1.val - cd.2.val := hgap
    have hpairs := primeCubic_difference_injective_of_same_positive_gap
      (Nat.le_of_lt hab'.1) (Nat.le_of_lt hcd'.1)
      (Nat.sub_pos_of_lt hab'.1) hgap_eq (hab'.2.trans hcd'.2.symm)
    apply Prod.ext
    · apply Fin.ext
      exact hpairs.1
    · apply Fin.ext
      exact hpairs.2

/-- The fixed-difference representation function has subpolynomial growth,
uniformly in the interval length. -/
theorem exists_card_positiveCubicDifferencePairs_rpow_bound
    {N m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((positiveCubicDifferencePairs N m).card : ℝ) ≤
        C * Real.rpow (m : ℝ) ε := by
  obtain ⟨C, hC, hbound⟩ := exists_divisor_rpow_bound hε
  refine ⟨C, hC, ?_⟩
  have hcount := card_positiveCubicDifferencePairs_le_divisors N m hm
  have hcountReal :
      ((positiveCubicDifferencePairs N m).card : ℝ) ≤
        (m.divisors.card : ℝ) := by exact_mod_cast hcount
  exact hcountReal.trans (hbound m (Nat.ne_of_gt hm))

/-- The forward shift of the cubic phase factors by the shift length. -/
theorem primeCubic_shift_sub_factorization (h m : ℕ) :
    (primeCubic (m + h) : ℤ) - primeCubic m =
      (h : ℤ) * (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1) := by
  rw [primeCubic_cast_int, primeCubic_cast_int]
  push_cast
  ring

/-- Two forward differences of the cubic phase are linear in the base
variable, with a factor from each shift. -/
theorem primeCubic_second_difference (h k m : ℕ) :
    ((primeCubic (m + h + k) : ℤ) - primeCubic (m + k)) -
      ((primeCubic (m + h) : ℤ) - primeCubic m) =
        (h : ℤ) * k * (6 * (m : ℤ) + 3 * h + 3 * k) := by
  simp only [primeCubic_cast_int]
  push_cast
  ring

/-- Positive second-difference frequencies, retaining the base variable.
The order of the coordinates is `(h, k, m)`. -/
def positiveCubicSecondDifferenceFiber (N M : ℕ) : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) :=
  (Finset.univ : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1)))).filter fun hkm =>
      0 < hkm.1.val ∧ 0 < hkm.2.1.val ∧
        hkm.2.2.val + hkm.1.val + hkm.2.1.val ≤ N ∧
          3 * hkm.1.val * hkm.2.1.val *
            (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val) = M

/-- Every frequency from the finite positive second-difference range is
strictly positive and below a cubic bound independent of the shifts. -/
theorem positiveCubicSecondDifferenceFiber_frequency_range
    {N M : ℕ} {hkm : Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))}
    (hhkm : hkm ∈ positiveCubicSecondDifferenceFiber N M) :
    0 < M ∧ M ≤ 6 * (N + 1) ^ 3 := by
  rcases (Finset.mem_filter.mp hhkm).2 with ⟨hh, hk, hbound, hfreq⟩
  have hinner : 0 < 2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val := by
    omega
  have hpos : 0 < M := by
    rw [← hfreq]
    positivity
  have hhlen : hkm.1.val ≤ N + 1 := by omega
  have hklen : hkm.2.1.val ≤ N + 1 := by omega
  have hmlen : 2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val ≤
      2 * (N + 1) := by omega
  refine ⟨hpos, ?_⟩
  rw [← hfreq]
  calc
    3 * hkm.1.val * hkm.2.1.val *
        (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val) ≤
      3 * (N + 1) * (N + 1) * (2 * (N + 1)) := by
        gcongr
    _ = 6 * (N + 1) ^ 3 := by ring

/-- The finite domain for both positive shifts and the base point. -/
def positiveCubicSecondDifferenceTriples (N : ℕ) : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) :=
  (Finset.univ : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1)))).filter fun hkm =>
      0 < hkm.1.val ∧ 0 < hkm.2.1.val ∧
        hkm.2.2.val + hkm.1.val + hkm.2.1.val ≤ N

/-- The frequency of a positive second-difference triple. -/
def cubicSecondDifferenceFrequency {N : ℕ}
    (hkm : Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) : ℕ :=
  3 * hkm.1.val * hkm.2.1.val *
    (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val)

theorem positiveCubicSecondDifferenceFiber_eq_filter
    (N M : ℕ) :
    positiveCubicSecondDifferenceFiber N M =
      (positiveCubicSecondDifferenceTriples N).filter fun hkm =>
        cubicSecondDifferenceFrequency hkm = M := by
  ext hkm
  simp [positiveCubicSecondDifferenceFiber,
    positiveCubicSecondDifferenceTriples,
    cubicSecondDifferenceFrequency, and_assoc]

/-- Summing all positive-frequency fiber sizes counts the valid triples
exactly; the total is at most the cube of the endpoint size. -/
theorem sum_card_positiveCubicSecondDifferenceFiber_le_cube (N : ℕ) :
    (∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
      (positiveCubicSecondDifferenceFiber N M).card) ≤ (N + 1) ^ 3 := by
  classical
  let s := positiveCubicSecondDifferenceTriples N
  let t := Finset.range (6 * (N + 1) ^ 3 + 1)
  have hmaps : Set.MapsTo (@cubicSecondDifferenceFrequency N)
      (s : Set _) (t : Set ℕ) := by
    intro hkm hhkm
    have hhkm' : hkm ∈
        positiveCubicSecondDifferenceFiber N
          (cubicSecondDifferenceFrequency hkm) := by
      rw [positiveCubicSecondDifferenceFiber_eq_filter]
      simp [s] at hhkm ⊢
      exact hhkm
    have hrange := positiveCubicSecondDifferenceFiber_frequency_range hhkm'
    exact Finset.mem_range.mpr (by omega)
  have hsum : s.card =
      ∑ M ∈ t, (positiveCubicSecondDifferenceFiber N M).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro M hM
    rw [positiveCubicSecondDifferenceFiber_eq_filter]
  have hcard : s.card ≤ (N + 1) ^ 3 := by
    calc
      s.card ≤ (Finset.univ : Finset
        (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1)))).card := by
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = (N + 1) ^ 3 := by simp [pow_succ, mul_comm]
  simpa only [t, ← hsum] using hcard

/-- A fixed positive second-difference frequency has at most two divisor
choices: the first shift and the product of the two shifts. Unlike the
third-difference fiber, this also determines the base variable. -/
theorem card_positiveCubicSecondDifferenceFiber_le_divisors_sq
    (N M : ℕ) (hM : 0 < M) :
    (positiveCubicSecondDifferenceFiber N M).card ≤
      M.divisors.card ^ 2 := by
  classical
  let f : (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) → ℕ × ℕ :=
    fun hkm => (hkm.1.val, hkm.1.val * hkm.2.1.val)
  have hcard : (positiveCubicSecondDifferenceFiber N M).card ≤
      (M.divisors.product M.divisors).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro hkm hhkm
      rw [Finset.mem_coe]
      rcases (Finset.mem_filter.mp hhkm).2 with
        ⟨hh, hk, hbound, hfreq⟩
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, hM.ne'⟩
        refine ⟨3 * hkm.2.1.val *
          (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val), ?_⟩
        calc
          M = 3 * hkm.1.val * hkm.2.1.val *
              (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val) :=
            hfreq.symm
          _ = hkm.1.val * (3 * hkm.2.1.val *
              (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val)) := by ring
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, hM.ne'⟩
        refine ⟨3 *
          (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val), ?_⟩
        calc
          M = 3 * hkm.1.val * hkm.2.1.val *
              (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val) :=
            hfreq.symm
          _ = (hkm.1.val * hkm.2.1.val) *
              (3 * (2 * hkm.2.2.val + hkm.1.val + hkm.2.1.val)) := by ring
    · intro x hx y hy hxy
      rcases (Finset.mem_filter.mp hx).2 with
        ⟨hxpos, hkxpos, hxbound, hxfreq⟩
      rcases (Finset.mem_filter.mp hy).2 with
        ⟨hypos, hkypos, hybound, hyfreq⟩
      have hh : x.1.val = y.1.val := congrArg Prod.fst hxy
      have hhk : x.1.val * x.2.1.val = y.1.val * y.2.1.val :=
        congrArg Prod.snd hxy
      have hk : x.2.1.val = y.2.1.val := by
        apply mul_left_cancel₀ (Nat.ne_of_gt hxpos)
        simpa [hh] using hhk
      have hcoef : 3 * x.1.val * x.2.1.val =
          3 * y.1.val * y.2.1.val := by rw [hh, hk]
      have hmexpr :
          2 * x.2.2.val + x.1.val + x.2.1.val =
            2 * y.2.2.val + y.1.val + y.2.1.val := by
        apply mul_left_cancel₀ (ne_of_gt
          (mul_pos (mul_pos (by decide : 0 < (3 : ℕ)) hxpos) hkxpos))
        calc
          (3 * x.1.val * x.2.1.val) *
              (2 * x.2.2.val + x.1.val + x.2.1.val) = M := hxfreq
          _ = (3 * y.1.val * y.2.1.val) *
              (2 * y.2.2.val + y.1.val + y.2.1.val) := hyfreq.symm
          _ = (3 * x.1.val * x.2.1.val) *
              (2 * y.2.2.val + y.1.val + y.2.1.val) := by rw [hcoef]
      have hm : x.2.2.val = y.2.2.val := by omega
      apply Prod.ext
      · exact Fin.ext hh
      · apply Prod.ext
        · exact Fin.ext hk
        · exact Fin.ext hm
  calc
    _ ≤ (M.divisors.product M.divisors).card := hcard
    _ = M.divisors.card ^ 2 := by simp [pow_two]

/-- The complete positive second-difference coefficient has arbitrarily
small power growth in its frequency. -/
theorem exists_positiveCubicSecondDifferenceFiber_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 0 < M →
      ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ≤
        C * Real.rpow (M : ℝ) ε := by
  obtain ⟨D, hD, hdiv⟩ := exists_divisor_rpow_bound (by linarith : 0 < ε / 2)
  refine ⟨D ^ 2, by positivity, fun N M hM ↦ ?_⟩
  have hcard := card_positiveCubicSecondDifferenceFiber_le_divisors_sq N M hM
  have hcardR :
      ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ≤
        (M.divisors.card : ℝ) ^ 2 := by exact_mod_cast hcard
  have hpoint := hdiv M hM.ne'
  have hpow : Real.rpow (M : ℝ) (ε / 2) ^ 2 =
      Real.rpow (M : ℝ) ε := by
    calc
      Real.rpow (M : ℝ) (ε / 2) ^ 2 =
          Real.rpow (M : ℝ) ((ε / 2) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast (by positivity) (ε / 2) 2).symm
      _ = Real.rpow (M : ℝ) ε := by congr 1; ring
  have hdivNonneg : 0 ≤ (M.divisors.card : ℝ) := by positivity
  have hboundNonneg : 0 ≤ D * Real.rpow (M : ℝ) (ε / 2) :=
    mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
  calc
    ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ≤
        (M.divisors.card : ℝ) ^ 2 := hcardR
    _ ≤ (D * Real.rpow (M : ℝ) (ε / 2)) ^ 2 :=
      (sq_le_sq₀ hdivNonneg hboundNonneg).2 hpoint
    _ = D ^ 2 * Real.rpow (M : ℝ) ε := by rw [mul_pow, hpow]

/-- Uniform coefficient bound on the entire cubic frequency range. -/
theorem exists_uniform_positiveCubicSecondDifferenceFiber_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 0 < M → M ≤ 6 * (N + 1) ^ 3 →
      ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ≤
        C * Real.rpow (N + 1 : ℝ) ε := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_positiveCubicSecondDifferenceFiber_rpow_bound
      (by linarith : 0 < ε / 3)
  let C : ℝ := D * Real.rpow 6 (ε / 3)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun N M hM hMle ↦ ?_⟩
  have hMreal : (M : ℝ) ≤ 6 * (N + 1 : ℝ) ^ 3 := by exact_mod_cast hMle
  have hpowle : Real.rpow (M : ℝ) (ε / 3) ≤
      Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) :=
    Real.rpow_le_rpow (by positivity) hMreal (by linarith)
  have hscale : Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) =
      Real.rpow 6 (ε / 3) * Real.rpow (N + 1 : ℝ) ε := by
    change (6 * (N + 1 : ℝ) ^ 3) ^ (ε / 3) = _
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    apply congrArg (fun x : ℝ => Real.rpow 6 (ε / 3) * x)
    calc
      Real.rpow ((N + 1 : ℝ) ^ 3) (ε / 3) =
          (Real.rpow (N + 1 : ℝ) (ε / 3)) ^ 3 :=
        (Real.rpow_pow_comm (by positivity) (ε / 3) 3).symm
      _ = Real.rpow (N + 1 : ℝ) ((ε / 3) * (3 : ℝ)) :=
        (Real.rpow_mul_natCast (by positivity) (ε / 3) 3).symm
      _ = Real.rpow (N + 1 : ℝ) ε := by congr 1; ring
  calc
    ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ≤
        D * Real.rpow (M : ℝ) (ε / 3) := hbound N M hM
    _ ≤ D * Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) :=
      mul_le_mul_of_nonneg_left hpowle hD.le
    _ = C * Real.rpow (N + 1 : ℝ) ε := by
      rw [hscale]
      dsimp [C]
      ring

theorem card_positiveCubicSecondDifferenceFiber_zero (N : ℕ) :
    (positiveCubicSecondDifferenceFiber N 0).card = 0 := by
  by_contra hzero
  obtain ⟨hkm, hhkm⟩ :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
  have hpos := (positiveCubicSecondDifferenceFiber_frequency_range hhkm).1
  omega

/-- Parseval will identify this finite squared sum with the `L²` norm of
the second-difference exponential sum. Its bound follows from the uniform
divisor estimate and exact counting of triples. -/
theorem exists_cubicSecondDifferenceCoefficientEnergy_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2) ≤
          C * Real.rpow (N + 1 : ℝ) ε * (N + 1 : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_positiveCubicSecondDifferenceFiber_rpow_bound hε
  refine ⟨C, hC, fun N ↦ ?_⟩
  let B : ℝ := C * Real.rpow (N + 1 : ℝ) ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum :
      (∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ)) ≤
          (N + 1 : ℝ) ^ 3 := by
    exact_mod_cast sum_card_positiveCubicSecondDifferenceFiber_le_cube N
  calc
    (∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2) ≤
      ∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        B * ((positiveCubicSecondDifferenceFiber N M).card : ℝ) := by
          apply Finset.sum_le_sum
          intro M hM
          by_cases hMpos : 0 < M
          · have hMle : M ≤ 6 * (N + 1) ^ 3 := by
              have hMlt := Finset.mem_range.mp hM
              omega
            have hpoint := hbound N M hMpos hMle
            calc
              ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2 =
                  ((positiveCubicSecondDifferenceFiber N M).card : ℝ) *
                    ((positiveCubicSecondDifferenceFiber N M).card : ℝ) :=
                pow_two _
              _ ≤ B * ((positiveCubicSecondDifferenceFiber N M).card : ℝ) :=
                mul_le_mul_of_nonneg_right hpoint (by positivity)
          · have hMzero : M = 0 := Nat.eq_zero_of_not_pos hMpos
            subst M
            simp [card_positiveCubicSecondDifferenceFiber_zero]
    _ = B * (∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ B * (N + 1 : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hsum hB
    _ = C * Real.rpow (N + 1 : ℝ) ε * (N + 1 : ℝ) ^ 3 := rfl

/-- The second-difference exponential sum grouped by its natural
frequency. A following identity will identify it with the triple sum. -/
noncomputable def cubicSecondDifferenceGroupedSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
    ((positiveCubicSecondDifferenceFiber N M).card : ℂ) * addChar α M

private theorem conj_cubicSecondDifferenceGroupedSum (α : ℝ) (N : ℕ) :
    conj (cubicSecondDifferenceGroupedSum α N) =
      ∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℂ) *
          negAddChar α M := by
  unfold cubicSecondDifferenceGroupedSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [map_mul, conj_addChar]
  simp

private theorem complex_ofReal_norm_sq (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  calc
    ((‖z‖ ^ 2 : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ) ^ 2) := by push_cast; rfl
    _ = z * conj z := by rw [Complex.mul_conj']

/-- Exact Parseval identity for the grouped second-difference sum. -/
theorem integral_norm_cubicSecondDifferenceGroupedSum_sq (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ((‖cubicSecondDifferenceGroupedSum α N‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2) : ℂ) := by
  classical
  let t := Finset.range (6 * (N + 1) ^ 3 + 1)
  let r : ℕ → ℕ := fun M =>
    (positiveCubicSecondDifferenceFiber N M).card
  have hpoint : ∀ α : ℝ,
      ((‖cubicSecondDifferenceGroupedSum α N‖ ^ 2 : ℝ) : ℂ) =
        ∑ M ∈ t, ∑ K ∈ t,
          ((r M * r K : ℕ) : ℂ) *
            (addChar α M * negAddChar α K) := by
    intro α
    rw [complex_ofReal_norm_sq, conj_cubicSecondDifferenceGroupedSum]
    unfold cubicSecondDifferenceGroupedSum
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro M hM
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    dsimp [r]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα => hpoint α)]
  rw [integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro M hM
    rw [integral_finsetSum]
    · calc
        (∑ K ∈ t,
          ∫ α in Set.Icc (0 : ℝ) 1,
            (r M : ℂ) * (r K : ℂ) *
              (addChar α M * negAddChar α K)) =
            ∑ K ∈ t, if M = K then (r M : ℂ) * (r K : ℂ) else 0 := by
              apply Finset.sum_congr rfl
              intro K hK
              rw [show
                  (∫ α in Set.Icc (0 : ℝ) 1,
                    (r M : ℂ) * (r K : ℂ) *
                      (addChar α M * negAddChar α K)) =
                    ((r M : ℂ) * (r K : ℂ)) *
                      ∫ α in Set.Icc (0 : ℝ) 1,
                        addChar α M * negAddChar α K by
                    rw [← integral_indicator measurableSet_Icc,
                      ← integral_indicator measurableSet_Icc]
                    simp_rw [Set.indicator_const_mul]
                    exact MeasureTheory.integral_const_mul _ _]
              rw [integral_addChar_mul_negAddChar]
              split_ifs <;> simp_all
        _ = ((positiveCubicSecondDifferenceFiber N M).card : ℂ) ^ 2 := by
          simp [hM, r, pow_two]
    · intro K hK
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro M hM
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- The real form of the grouped Parseval identity. -/
theorem integral_norm_cubicSecondDifferenceGroupedSum_sq_real (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖cubicSecondDifferenceGroupedSum α N‖ ^ 2) =
      ∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hparseval := integral_norm_cubicSecondDifferenceGroupedSum_sq N
  push_cast
  push_cast at hparseval
  exact hparseval

/-- The positive second-difference sum before collecting equal frequencies. -/
noncomputable def cubicSecondDifferenceTripleSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ hkm ∈ positiveCubicSecondDifferenceTriples N,
    addChar α (cubicSecondDifferenceFrequency hkm)

theorem cubicSecondDifferenceTripleSum_eq_grouped (α : ℝ) (N : ℕ) :
    cubicSecondDifferenceTripleSum α N =
      cubicSecondDifferenceGroupedSum α N := by
  classical
  let s := positiveCubicSecondDifferenceTriples N
  let t := Finset.range (6 * (N + 1) ^ 3 + 1)
  have hmaps : ∀ hkm ∈ s, cubicSecondDifferenceFrequency hkm ∈ t := by
    intro hkm hhkm
    have hhkm' : hkm ∈
        positiveCubicSecondDifferenceFiber N
          (cubicSecondDifferenceFrequency hkm) := by
      rw [positiveCubicSecondDifferenceFiber_eq_filter]
      simp [s] at hhkm ⊢
      exact hhkm
    have hrange := positiveCubicSecondDifferenceFiber_frequency_range hhkm'
    exact Finset.mem_range.mpr (by omega)
  change (∑ hkm ∈ s, addChar α (cubicSecondDifferenceFrequency hkm)) =
    ∑ M ∈ t,
      ((positiveCubicSecondDifferenceFiber N M).card : ℂ) * addChar α M
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun hkm => addChar α (cubicSecondDifferenceFrequency hkm))]
  apply Finset.sum_congr rfl
  intro M hM
  have hfiber :
      (s.filter fun hkm => cubicSecondDifferenceFrequency hkm = M) =
        positiveCubicSecondDifferenceFiber N M := by
    simpa only [s] using (positiveCubicSecondDifferenceFiber_eq_filter N M).symm
  rw [hfiber]
  have hterm :
      (∑ hkm ∈ positiveCubicSecondDifferenceFiber N M,
        addChar α (cubicSecondDifferenceFrequency hkm)) =
        ∑ _hkm ∈ positiveCubicSecondDifferenceFiber N M,
          addChar α M := by
    apply Finset.sum_congr rfl
    intro hkm hhkm
    have hfreq := (Finset.mem_filter.mp
      ((positiveCubicSecondDifferenceFiber_eq_filter N M).symm ▸ hhkm)).2
    rw [hfreq]
  rw [hterm]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Parseval for the actual sum over positive second-difference triples. -/
theorem integral_norm_cubicSecondDifferenceTripleSum_sq (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖cubicSecondDifferenceTripleSum α N‖ ^ 2) =
      ∑ M ∈ Finset.range (6 * (N + 1) ^ 3 + 1),
        ((positiveCubicSecondDifferenceFiber N M).card : ℝ) ^ 2 := by
  simp_rw [cubicSecondDifferenceTripleSum_eq_grouped]
  exact integral_norm_cubicSecondDifferenceGroupedSum_sq_real N

/-- The genuine second-difference `L²` bound, with the base variable
counted in every coefficient. -/
theorem exists_cubicSecondDifferenceTripleSum_energy_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∫ α in Set.Icc (0 : ℝ) 1,
        ‖cubicSecondDifferenceTripleSum α N‖ ^ 2) ≤
          C * Real.rpow (N + 1 : ℝ) ε * (N + 1 : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_cubicSecondDifferenceCoefficientEnergy_bound hε
  refine ⟨C, hC, fun N ↦ ?_⟩
  rw [integral_norm_cubicSecondDifferenceTripleSum_sq]
  exact hbound N

/-- Three forward differences of the cubic phase, as an integer frequency. -/
def primeCubicThirdDifference (h k l m : ℕ) : ℤ :=
    (((primeCubic (m + l + h + k) : ℤ) - primeCubic (m + l + k)) -
      ((primeCubic (m + l + h) : ℤ) - primeCubic (m + l))) -
      (((primeCubic (m + h + k) : ℤ) - primeCubic (m + k)) -
        ((primeCubic (m + h) : ℤ) - primeCubic m))

/-- Three forward differences of the cubic phase are the constant
`6hkl`. This is the algebraic endpoint of Hua's cubic differencing. -/
theorem primeCubic_third_difference (h k l m : ℕ) :
    primeCubicThirdDifference h k l m = 6 * (h : ℤ) * k * l := by
  unfold primeCubicThirdDifference
  simp only [primeCubic_cast_int]
  push_cast
  ring

/-- The absolute terminal frequency after three cubic differences is the
natural product `6hkl`. -/
theorem natAbs_primeCubicThirdDifference (h k l m : ℕ) :
    (primeCubicThirdDifference h k l m).natAbs = 6 * h * k * l := by
  rw [primeCubic_third_difference]
  have hcast : (6 : ℤ) * (h : ℤ) * k * l =
      ((6 * h * k * l : ℕ) : ℤ) := by push_cast; ring
  rw [hcast]
  rw [Int.natAbs_natCast]

/-- Finite positive factorizations of a fixed target into the three
differencing shifts, with the cubic third-difference coefficient `6`. -/
def positiveCubicThirdDifferenceShiftFiber (N M : ℕ) : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) :=
  (Finset.univ : Finset
    (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1)))).filter fun hkl =>
      0 < hkl.1.val ∧ 0 < hkl.2.1.val ∧ 0 < hkl.2.2.val ∧
        6 * hkl.1.val * hkl.2.1.val * hkl.2.2.val = M

/-- Choosing the first shift and the product of the first two shifts embeds a
positive triple factorization fiber into a product of two divisor sets. -/
theorem card_positiveCubicThirdDifferenceShiftFiber_le_divisors_sq
    (N M : ℕ) (hM : 0 < M) :
    (positiveCubicThirdDifferenceShiftFiber N M).card ≤
      M.divisors.card ^ 2 := by
  classical
  let f : (Fin (N + 1) × (Fin (N + 1) × Fin (N + 1))) → ℕ × ℕ :=
    fun hkl => (hkl.1.val, hkl.1.val * hkl.2.1.val)
  have hcard : (positiveCubicThirdDifferenceShiftFiber N M).card ≤
      (M.divisors.product M.divisors).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro hkl hhkl
      rw [Finset.mem_coe]
      have hhkl' := (Finset.mem_filter.mp hhkl).2
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, hM.ne'⟩
        refine ⟨6 * hkl.2.1.val * hkl.2.2.val, ?_⟩
        calc
          M = 6 * hkl.1.val * hkl.2.1.val * hkl.2.2.val :=
            hhkl'.2.2.2.symm
          _ = hkl.1.val * (6 * hkl.2.1.val * hkl.2.2.val) := by ring
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, hM.ne'⟩
        refine ⟨6 * hkl.2.2.val, ?_⟩
        calc
          M = 6 * hkl.1.val * hkl.2.1.val * hkl.2.2.val :=
            hhkl'.2.2.2.symm
          _ = (hkl.1.val * hkl.2.1.val) * (6 * hkl.2.2.val) := by ring
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have hh : x.1.val = y.1.val := congrArg Prod.fst hxy
      have hhk : x.1.val * x.2.1.val = y.1.val * y.2.1.val :=
        congrArg Prod.snd hxy
      have hk : x.2.1.val = y.2.1.val := by
        apply mul_left_cancel₀ (Nat.ne_of_gt hx'.1)
        simpa [hh] using hhk
      have hcoef : 6 * x.1.val * x.2.1.val =
          6 * y.1.val * y.2.1.val := by rw [hh, hk]
      have hl : x.2.2.val = y.2.2.val := by
        apply mul_left_cancel₀ (ne_of_gt
          (mul_pos (mul_pos (by decide : 0 < (6 : ℕ)) hx'.1) hx'.2.1))
        calc
          (6 * x.1.val * x.2.1.val) * x.2.2.val = M := hx'.2.2.2
          _ = (6 * y.1.val * y.2.1.val) * y.2.2.val :=
            hy'.2.2.2.symm
          _ = (6 * x.1.val * x.2.1.val) * y.2.2.val := by rw [hcoef]
      apply Prod.ext
      · exact Fin.ext hh
      · apply Prod.ext
        · exact Fin.ext hk
        · exact Fin.ext hl
  calc
    _ ≤ (M.divisors.product M.divisors).card := hcard
    _ = M.divisors.card ^ 2 := by simp [pow_two]

/-- Uniform subpolynomial control of every positive third-difference shift
fiber. This is the pointwise coefficient bound used before summing over
frequencies in Hua's differencing argument. -/
theorem exists_positiveCubicThirdDifferenceShiftFiber_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 0 < M →
      ((positiveCubicThirdDifferenceShiftFiber N M).card : ℝ) ≤
        C * Real.rpow (M : ℝ) ε := by
  obtain ⟨D, hD, hdiv⟩ := exists_divisor_rpow_bound (by linarith : 0 < ε / 2)
  refine ⟨D ^ 2, by positivity, fun N M hM ↦ ?_⟩
  have hcard := card_positiveCubicThirdDifferenceShiftFiber_le_divisors_sq
    N M hM
  have hcardR :
      ((positiveCubicThirdDifferenceShiftFiber N M).card : ℝ) ≤
        (M.divisors.card : ℝ) ^ 2 := by exact_mod_cast hcard
  have hpoint := hdiv M hM.ne'
  have hpow : Real.rpow (M : ℝ) (ε / 2) ^ 2 =
      Real.rpow (M : ℝ) ε := by
    calc
      Real.rpow (M : ℝ) (ε / 2) ^ 2 =
          Real.rpow (M : ℝ) ((ε / 2) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast (by positivity) (ε / 2) 2).symm
      _ = Real.rpow (M : ℝ) ε := by congr 1; ring
  have hdivNonneg : 0 ≤ (M.divisors.card : ℝ) := by positivity
  have hboundNonneg : 0 ≤ D * Real.rpow (M : ℝ) (ε / 2) :=
    mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
  calc
    ((positiveCubicThirdDifferenceShiftFiber N M).card : ℝ) ≤
        (M.divisors.card : ℝ) ^ 2 := hcardR
    _ ≤ (D * Real.rpow (M : ℝ) (ε / 2)) ^ 2 :=
      (sq_le_sq₀ hdivNonneg hboundNonneg).2 hpoint
    _ = D ^ 2 * Real.rpow (M : ℝ) ε := by rw [mul_pow, hpow]

/-- Uniformly over all terminal frequencies of size at most the cubic
differencing range, the positive shift-fiber multiplicity is at most an
arbitrarily small power of the interval length. -/
theorem exists_uniform_positiveCubicThirdDifferenceShiftFiber_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 0 < M → M ≤ 6 * (N + 1) ^ 3 →
      ((positiveCubicThirdDifferenceShiftFiber N M).card : ℝ) ≤
        C * Real.rpow (N + 1 : ℝ) ε := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_positiveCubicThirdDifferenceShiftFiber_rpow_bound
      (by linarith : 0 < ε / 3)
  let C : ℝ := D * Real.rpow 6 (ε / 3)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun N M hM hMle ↦ ?_⟩
  have hMreal : (M : ℝ) ≤ 6 * (N + 1 : ℝ) ^ 3 := by exact_mod_cast hMle
  have hpowle : Real.rpow (M : ℝ) (ε / 3) ≤
      Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) :=
    Real.rpow_le_rpow (by positivity) hMreal (by linarith)
  have hscale : Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) =
      Real.rpow 6 (ε / 3) * Real.rpow (N + 1 : ℝ) ε := by
    change (6 * (N + 1 : ℝ) ^ 3) ^ (ε / 3) = _
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    apply congrArg (fun x : ℝ => Real.rpow 6 (ε / 3) * x)
    calc
      Real.rpow ((N + 1 : ℝ) ^ 3) (ε / 3) =
          (Real.rpow (N + 1 : ℝ) (ε / 3)) ^ 3 :=
        (Real.rpow_pow_comm (by positivity) (ε / 3) 3).symm
      _ = Real.rpow (N + 1 : ℝ) ((ε / 3) * (3 : ℝ)) :=
        (Real.rpow_mul_natCast (by positivity) (ε / 3) 3).symm
      _ = Real.rpow (N + 1 : ℝ) ε := by congr 1; ring
  calc
    ((positiveCubicThirdDifferenceShiftFiber N M).card : ℝ) ≤
        D * Real.rpow (M : ℝ) (ε / 3) := hbound N M hM
    _ ≤ D * Real.rpow (6 * (N + 1 : ℝ) ^ 3) (ε / 3) :=
      mul_le_mul_of_nonneg_left hpowle hD.le
    _ = C * Real.rpow (N + 1 : ℝ) ε := by
      rw [hscale]
      dsimp [C]
      ring

/-- When all three shifts are positive, the terminal frequency in cubic
differencing is nonzero, so its integral over a full period vanishes. -/
theorem integral_exp_primeCubicThirdDifference_eq_zero
    {h k l m : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * Complex.I *
        (primeCubicThirdDifference h k l m : ℂ) * (α : ℂ))) = 0 := by
  rw [integral_exp_int_frequency]
  have hnonzero : primeCubicThirdDifference h k l m ≠ 0 := by
    rw [primeCubic_third_difference]
    have hhZ : (0 : ℤ) < h := by exact_mod_cast hh
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
    positivity
  simp [hnonzero]

/-- In the fourth-moment shift equation, every nonzero positive shift divides
the difference of the two base cubic phases. -/
theorem shift_dvd_base_difference_of_cubic_relation
    {a b h m : ℕ}
    (heq : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic (m + h) : ℤ) - primeCubic m) = 0) :
    (h : ℤ) ∣ (primeCubic a : ℤ) - primeCubic b := by
  have hfactor := primeCubic_shift_sub_factorization h m
  have hbase : (primeCubic a : ℤ) - primeCubic b =
      -((primeCubic (m + h) : ℤ) - primeCubic m) := by linarith
  rw [hbase, hfactor]
  exact dvd_neg.mpr ⟨3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1, by ring⟩

/-- The backward-shift orientation gives the same divisor condition. -/
theorem shift_dvd_base_difference_of_backward_cubic_relation
    {a b h m : ℕ}
    (heq : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic m : ℤ) - primeCubic (m + h)) = 0) :
    (h : ℤ) ∣ (primeCubic a : ℤ) - primeCubic b := by
  have hfactor := primeCubic_shift_sub_factorization h m
  have hbase : (primeCubic a : ℤ) - primeCubic b =
      (primeCubic (m + h) : ℤ) - primeCubic m := by linarith
  rw [hbase, hfactor]
  exact ⟨3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1, rfl⟩

/-- For fixed positive shift, the quadratic coefficient in the shift
difference is strictly increasing in the base variable. -/
theorem cubicShiftQuadratic_injective {h : ℕ} (hh : 0 < h) :
    Function.Injective (fun m : ℕ =>
      (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1)) := by
  intro a b hab
  change (3 * (a : ℤ) ^ 2 + 3 * h * a + h ^ 2 - 1) =
    (3 * (b : ℤ) ^ 2 + 3 * h * b + h ^ 2 - 1) at hab
  rcases lt_trichotomy a b with hab' | hab' | hab'
  · have hdiff :
        (3 * (b : ℤ) ^ 2 + 3 * h * b + h ^ 2 - 1) -
          (3 * (a : ℤ) ^ 2 + 3 * h * a + h ^ 2 - 1) =
            3 * ((b : ℤ) - a) * ((a : ℤ) + b + h) := by ring
    have hpos : (0 : ℤ) < 3 * ((b : ℤ) - a) * ((a : ℤ) + b + h) := by
      have hbgt : (a : ℤ) < b := by exact_mod_cast hab'
      have hhpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
      positivity
    rw [← hdiff] at hpos
    have hval : (3 * (a : ℤ) ^ 2 + 3 * h * a + h ^ 2 - 1) <
        (3 * (b : ℤ) ^ 2 + 3 * h * b + h ^ 2 - 1) := by linarith
    exact (ne_of_lt hval) hab |>.elim
  · exact hab'
  · have hdiff :
        (3 * (a : ℤ) ^ 2 + 3 * h * a + h ^ 2 - 1) -
          (3 * (b : ℤ) ^ 2 + 3 * h * b + h ^ 2 - 1) =
            3 * ((a : ℤ) - b) * ((a : ℤ) + b + h) := by ring
    have hpos : (0 : ℤ) < 3 * ((a : ℤ) - b) * ((a : ℤ) + b + h) := by
      have habgt : (b : ℤ) < a := by exact_mod_cast hab'
      have hhpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
      positivity
    rw [← hdiff] at hpos
    have hval : (3 * (b : ℤ) ^ 2 + 3 * h * b + h ^ 2 - 1) <
        (3 * (a : ℤ) ^ 2 + 3 * h * a + h ^ 2 - 1) := by linarith
    exact (ne_of_gt hval) hab |>.elim

/-- For fixed base phases and a nonzero positive shift, the shift equation
determines the shifted base variable uniquely in the forward orientation. -/
theorem eq_of_same_forward_cubic_shift_relation
    {a b h m n : ℕ} (hh : 0 < h)
    (hm : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic (m + h) : ℤ) - primeCubic m) = 0)
    (hn : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic (n + h) : ℤ) - primeCubic n) = 0) : m = n := by
  have hfacm := primeCubic_shift_sub_factorization h m
  have hfacn := primeCubic_shift_sub_factorization h n
  have hmul : (h : ℤ) * (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1) =
      (h : ℤ) * (3 * (n : ℤ) ^ 2 + 3 * h * n + h ^ 2 - 1) := by
    rw [← hfacm, ← hfacn]
    linarith
  have hq := mul_left_cancel₀ (by exact_mod_cast hh.ne') hmul
  have hmcast := cubicShiftQuadratic_injective hh hq
  exact hmcast

/-- For fixed base phases and a nonzero positive shift, the shift equation
determines the shifted base variable uniquely in the backward orientation. -/
theorem eq_of_same_backward_cubic_shift_relation
    {a b h m n : ℕ} (hh : 0 < h)
    (hm : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic m : ℤ) - primeCubic (m + h)) = 0)
    (hn : (primeCubic a : ℤ) - primeCubic b +
      ((primeCubic n : ℤ) - primeCubic (n + h)) = 0) : m = n := by
  have hfacm := primeCubic_shift_sub_factorization h m
  have hfacn := primeCubic_shift_sub_factorization h n
  have hbackm : (primeCubic m : ℤ) - primeCubic (m + h) =
      -((h : ℤ) * (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1)) := by
    rw [← hfacm]
    ring
  have hbackn : (primeCubic n : ℤ) - primeCubic (n + h) =
      -((h : ℤ) * (3 * (n : ℤ) ^ 2 + 3 * h * n + h ^ 2 - 1)) := by
    rw [← hfacn]
    ring
  have hmul : (h : ℤ) * (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1) =
      (h : ℤ) * (3 * (n : ℤ) ^ 2 + 3 * h * n + h ^ 2 - 1) := by
    rw [hbackm] at hm
    rw [hbackn] at hn
    linarith
  have hq := mul_left_cancel₀ (by exact_mod_cast hh.ne') hmul
  have hmcast := cubicShiftQuadratic_injective hh hq
  exact hmcast

/-- Finite set of positive forward shifts and base variables solving the
fourth-moment shifted equation for fixed outer variables. The interval bounds
are deliberately only used to make the set finite; no unproved analytic
estimate is built into this definition. -/
def forwardCubicShiftFiber (N a b : ℕ) : Finset
    (Fin (N + 1) × Fin (N + 1)) :=
  (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).filter fun hm =>
    0 < hm.1.val ∧
      (primeCubic a : ℤ) - primeCubic b +
        ((primeCubic (hm.2.val + hm.1.val) : ℤ) -
          primeCubic hm.2.val) = 0

/-- For fixed outer variables, a positive shift and its base variable are
uniquely determined among solutions of the forward fourth-moment relation.
Consequently, projection of the finite solution fiber to its shift is
injective. -/
theorem forwardCubicShiftFiber_shift_injective (N a b : ℕ) :
    Set.InjOn (fun hm : Fin (N + 1) × Fin (N + 1) ↦ hm.1.val)
      (forwardCubicShiftFiber N a b : Set (Fin (N + 1) × Fin (N + 1))) := by
  intro x hx y hy hxy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hh : x.1.val = y.1.val := hxy
  apply Prod.ext
  · exact Fin.ext hh
  · apply Fin.ext
    apply eq_of_same_forward_cubic_shift_relation
      (Nat.lt_of_lt_of_eq hx'.1 hh)
      (by simpa [hh] using hx'.2) hy'.2

/-- The number of solutions in a fixed forward shift fiber is bounded by the
divisor count of the absolute outer phase difference. This is the precise
finite divisor-sum reduction: each shift divides that difference and each
admissible shift contributes at most one base variable. -/
theorem card_forwardCubicShiftFiber_le_divisors
    (N a b : ℕ) (houter : primeCubic a ≠ primeCubic b) :
    (forwardCubicShiftFiber N a b).card ≤
      ((primeCubic a : ℤ) - primeCubic b).natAbs.divisors.card := by
  let D : ℤ := (primeCubic a : ℤ) - primeCubic b
  let shift : (Fin (N + 1) × Fin (N + 1)) → ℕ := fun hm => hm.1.val
  have hD : D.natAbs ≠ 0 := by
    intro hzero
    have hz : D = 0 := (Int.natAbs_eq_zero).mp hzero
    exact houter (by dsimp [D] at hz ⊢; omega)
  refine Finset.card_le_card_of_injOn shift ?_ ?_
  · intro hm hmem
    rw [Finset.mem_coe]
    have hm' := (Finset.mem_filter.mp hmem).2
    have hdivZ : (shift hm : ℤ) ∣ D := by
      dsimp [shift, D]
      exact shift_dvd_base_difference_of_cubic_relation hm'.2
    have hdiv : shift hm ∣ D.natAbs := by
      exact (Int.ofNat_dvd_left).mp hdivZ
    exact Nat.mem_divisors.mpr ⟨hdiv, hD⟩
  · exact forwardCubicShiftFiber_shift_injective N a b

/-- The backward-shift solution fiber, for fixed outer variables. -/
def backwardCubicShiftFiber (N a b : ℕ) : Finset
    (Fin (N + 1) × Fin (N + 1)) :=
  (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).filter fun hm =>
    0 < hm.1.val ∧
      (primeCubic a : ℤ) - primeCubic b +
        ((primeCubic hm.2.val : ℤ) -
          primeCubic (hm.2.val + hm.1.val)) = 0

/-- Projection of a fixed backward-shift solution fiber to its shift is
injective, by uniqueness of the base variable for a fixed positive shift. -/
theorem backwardCubicShiftFiber_shift_injective (N a b : ℕ) :
    Set.InjOn (fun hm : Fin (N + 1) × Fin (N + 1) ↦ hm.1.val)
      (backwardCubicShiftFiber N a b : Set (Fin (N + 1) × Fin (N + 1))) := by
  intro x hx y hy hxy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hh : x.1.val = y.1.val := hxy
  apply Prod.ext
  · exact Fin.ext hh
  · apply Fin.ext
    apply eq_of_same_backward_cubic_shift_relation
      (Nat.lt_of_lt_of_eq hx'.1 hh)
      (by simpa [hh] using hx'.2) hy'.2

/-- The backward fourth-moment shift fiber is likewise bounded by the divisor
count of the absolute outer phase difference. -/
theorem card_backwardCubicShiftFiber_le_divisors
    (N a b : ℕ) (houter : primeCubic a ≠ primeCubic b) :
    (backwardCubicShiftFiber N a b).card ≤
      ((primeCubic a : ℤ) - primeCubic b).natAbs.divisors.card := by
  let D : ℤ := (primeCubic a : ℤ) - primeCubic b
  let shift : (Fin (N + 1) × Fin (N + 1)) → ℕ := fun hm => hm.1.val
  have hD : D.natAbs ≠ 0 := by
    intro hzero
    have hz : D = 0 := (Int.natAbs_eq_zero).mp hzero
    exact houter (by dsimp [D] at hz ⊢; omega)
  refine Finset.card_le_card_of_injOn shift ?_ ?_
  · intro hm hmem
    rw [Finset.mem_coe]
    have hm' := (Finset.mem_filter.mp hmem).2
    have hdivZ : (shift hm : ℤ) ∣ D := by
      dsimp [shift, D]
      exact shift_dvd_base_difference_of_backward_cubic_relation hm'.2
    have hdiv : shift hm ∣ D.natAbs := by
      exact (Int.ofNat_dvd_left).mp hdivZ
    exact Nat.mem_divisors.mpr ⟨hdiv, hD⟩
  · exact backwardCubicShiftFiber_shift_injective N a b

/-- A zero forward increment with positive shift occurs only for the single
exception `0 ↦ 1`, reflecting the two zeroes of `x^3-x` on naturals. -/
theorem positive_cubic_shift_eq_zero_iff_exception
    {h m : ℕ} (hh : 0 < h)
    (heq : primeCubic (m + h) = primeCubic m) :
    h = 1 ∧ m = 0 := by
  have hfactor := primeCubic_shift_sub_factorization h m
  have heqZ : (primeCubic (m + h) : ℤ) = (primeCubic m : ℤ) := by
    exact_mod_cast heq
  have hdiff :
      (primeCubic (m + h) : ℤ) - primeCubic m = 0 :=
    sub_eq_zero.mpr heqZ
  have hzero : (h : ℤ) *
      (3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1) = 0 := by
    rw [← hfactor]
    exact hdiff
  have hhZ : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
  have hquad :
      3 * (m : ℤ) ^ 2 + 3 * h * m + h ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hhZ
  have hhnat : h = 1 := by
    by_contra hne
    have hge : 2 ≤ h := by omega
    have hgeZ : (2 : ℤ) ≤ h := by exact_mod_cast hge
    have hmZ : (0 : ℤ) ≤ m := by positivity
    nlinarith [sq_nonneg (m : ℤ)]
  constructor
  · exact hhnat
  · have hquad' := hquad
    rw [hhnat] at hquad'
    have hmZ : (0 : ℤ) ≤ m := by positivity
    have hmzero : (m : ℤ) = 0 := by nlinarith [sq_nonneg (m : ℤ)]
    exact_mod_cast hmzero

/-- If the outer phases agree, each positive forward-shift solution must be
the exceptional shift/base pair `(1,0)`. -/
theorem card_forwardCubicShiftFiber_le_one_of_equal_outer
    (N a b : ℕ) (houter : primeCubic a = primeCubic b) :
    (forwardCubicShiftFiber N a b).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxval := positive_cubic_shift_eq_zero_iff_exception hx'.1 (by
    have h := hx'.2
    rw [houter] at h
    have hdiff :
        (primeCubic (x.2.val + x.1.val) : ℤ) - primeCubic x.2.val = 0 := by
      omega
    exact_mod_cast (sub_eq_zero.mp hdiff))
  have hyval := positive_cubic_shift_eq_zero_iff_exception hy'.1 (by
    have h := hy'.2
    rw [houter] at h
    have hdiff :
        (primeCubic (y.2.val + y.1.val) : ℤ) - primeCubic y.2.val = 0 := by
      omega
    exact_mod_cast (sub_eq_zero.mp hdiff))
  apply Prod.ext
  · exact Fin.ext (by rw [hxval.1, hyval.1])
  · exact Fin.ext (by rw [hxval.2, hyval.2])

/-- Equal outer phases leave only the same exceptional positive shift in the
backward orientation. -/
theorem card_backwardCubicShiftFiber_le_one_of_equal_outer
    (N a b : ℕ) (houter : primeCubic a = primeCubic b) :
    (backwardCubicShiftFiber N a b).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxval := positive_cubic_shift_eq_zero_iff_exception hx'.1 (by
    have h := hx'.2
    rw [houter] at h
    have hdiff :
        (primeCubic (x.2.val + x.1.val) : ℤ) - primeCubic x.2.val = 0 := by
      omega
    exact_mod_cast (sub_eq_zero.mp hdiff))
  have hyval := positive_cubic_shift_eq_zero_iff_exception hy'.1 (by
    have h := hy'.2
    rw [houter] at h
    have hdiff :
        (primeCubic (y.2.val + y.1.val) : ℤ) - primeCubic y.2.val = 0 := by
      omega
    exact_mod_cast (sub_eq_zero.mp hdiff))
  have hxpair := hxval
  have hypair := hyval
  apply Prod.ext
  · exact Fin.ext (by rw [hxpair.1, hypair.1])
  · exact Fin.ext (by rw [hxpair.2, hypair.2])

/-- Aggregate count of the two positive-shift orientations over all outer
variable pairs. -/
def cubicPositiveFourthShiftCount (N : ℕ) : ℕ :=
  ∑ ab : Fin (N + 1) × Fin (N + 1),
    ((forwardCubicShiftFiber N ab.1.val ab.2.val).card +
      (backwardCubicShiftFiber N ab.1.val ab.2.val).card)

/-- The zero-shift contribution: when the shift is zero, the inner base
variable is free and the outer cubic phases must agree. -/
def cubicZeroFourthShiftCount (N : ℕ) : ℕ :=
  ∑ ab : Fin (N + 1) × Fin (N + 1),
    ∑ _m : Fin (N + 1),
      if primeCubic ab.1.val = primeCubic ab.2.val then 1 else 0

/-- Reindexing the positive-shift count by its outer pair gives a divisor-sum
bound. Equal outer phases are kept as an explicit finite exceptional term;
this avoids pretending that the divisor set of zero controls positive shifts.
The zero-shift contribution is included separately and bounded trivially. -/
theorem cubicFourthShiftCount_le_divisor_sum (N : ℕ) :
    cubicPositiveFourthShiftCount N + cubicZeroFourthShiftCount N ≤
      (∑ ab : Fin (N + 1) × Fin (N + 1),
        if primeCubic ab.1.val ≠ primeCubic ab.2.val then
          2 * ((primeCubic ab.1.val : ℤ) -
            primeCubic ab.2.val).natAbs.divisors.card
        else 2 * (N + 1) ^ 2) + (N + 1) ^ 3 := by
  classical
  let A := Fin (N + 1)
  have hpos : cubicPositiveFourthShiftCount N ≤
      ∑ ab : A × A,
        if primeCubic ab.1.val ≠ primeCubic ab.2.val then
          2 * ((primeCubic ab.1.val : ℤ) -
            primeCubic ab.2.val).natAbs.divisors.card
        else 2 * (N + 1) ^ 2 := by
    unfold cubicPositiveFourthShiftCount
    apply Finset.sum_le_sum
    intro ab _hab
    by_cases hneq : primeCubic ab.1.val ≠ primeCubic ab.2.val
    · have hf := card_forwardCubicShiftFiber_le_divisors N
        ab.1.val ab.2.val hneq
      have hb := card_backwardCubicShiftFiber_le_divisors N
        ab.1.val ab.2.val hneq
      simp [hneq]
      omega
    · have hf : (forwardCubicShiftFiber N ab.1.val ab.2.val).card ≤
          (N + 1) ^ 2 := by
        calc
          _ ≤ (Finset.univ : Finset (A × A)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = (N + 1) ^ 2 := by simp [A, pow_two]
      have hb : (backwardCubicShiftFiber N ab.1.val ab.2.val).card ≤
          (N + 1) ^ 2 := by
        calc
          _ ≤ (Finset.univ : Finset (A × A)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = (N + 1) ^ 2 := by simp [A, pow_two]
      simp [hneq]
      omega
  have hzero : cubicZeroFourthShiftCount N ≤ (N + 1) ^ 3 := by
    unfold cubicZeroFourthShiftCount
    calc
      _ ≤ ∑ _ab : A × A, (N + 1) := by
        apply Finset.sum_le_sum
        intro ab _hab
        calc
          (∑ _m : A,
            if primeCubic ab.1.val = primeCubic ab.2.val then 1 else 0)
              ≤ ∑ _m : A, 1 := by
                apply Finset.sum_le_sum
                intro m _hm
                split_ifs <;> omega
          _ = N + 1 := by simp [A]
      _ = (N + 1) ^ 3 := by simp [A, pow_succ]
  unfold cubicPositiveFourthShiftCount cubicZeroFourthShiftCount
  exact Nat.add_le_add hpos hzero


/-- One ε-dependent constant controls every positive cubic-difference fiber,
independently of the interval length and the difference. -/
theorem exists_uniform_positiveCubicDifferencePairs_bound {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, 0 < m →
      ((positiveCubicDifferencePairs N m).card : ℝ) ≤
        C * Real.rpow (m : ℝ) ε := by
  obtain ⟨C, hC, hbound⟩ := exists_divisor_rpow_bound hε
  refine ⟨C, hC, fun N m hm ↦ ?_⟩
  have hcount := card_positiveCubicDifferencePairs_le_divisors N m hm
  have hcountReal :
      ((positiveCubicDifferencePairs N m).card : ℝ) ≤
        (m.divisors.card : ℝ) := by exact_mod_cast hcount
  exact hcountReal.trans (hbound m (Nat.ne_of_gt hm))

/-- The second moment of positive cubic-difference multiplicities up to `M`.
This is a basic additive-energy quantity for the differencing argument. -/
def positiveCubicDifferencePairEnergy (N M : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 M, (positiveCubicDifferencePairs N m).card ^ 2

/-- The divisor estimate gives a uniform second-moment bound for the
positive-difference representation function. -/
theorem positiveCubicDifferencePairEnergy_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 0 < M →
      (positiveCubicDifferencePairEnergy N M : ℝ) ≤
        (M : ℝ) * (C * Real.rpow (M : ℝ) ε) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ := exists_uniform_positiveCubicDifferencePairs_bound hε
  refine ⟨C, hC, fun N M hM ↦ ?_⟩
  have hcast :
      (positiveCubicDifferencePairEnergy N M : ℝ) =
        ∑ m ∈ Finset.Icc 1 M,
          ((positiveCubicDifferencePairs N m).card : ℝ) ^ 2 := by
    simp [positiveCubicDifferencePairEnergy, Nat.cast_sum, Nat.cast_pow]
  rw [hcast]
  calc
    _ ≤ ∑ _m ∈ Finset.Icc 1 M,
        (C * Real.rpow (M : ℝ) ε) ^ 2 := by
          apply Finset.sum_le_sum
          intro m hm
          have hm' := (Finset.mem_Icc.mp hm)
          have hmpos : 0 < m := Nat.lt_of_lt_of_le (by omega) hm'.1
          have hpow : Real.rpow (m : ℝ) ε ≤ Real.rpow (M : ℝ) ε := by
            apply Real.rpow_le_rpow
            · exact_mod_cast (Nat.zero_le m)
            · exact_mod_cast hm'.2
            · exact hε.le
          have hpoint := hpair N m hmpos
          calc
            ((positiveCubicDifferencePairs N m).card : ℝ) ^ 2 ≤
                (C * Real.rpow (m : ℝ) ε) ^ 2 := by
                  have hnonneg : 0 ≤ C * Real.rpow (m : ℝ) ε :=
                    mul_nonneg hC.le (Real.rpow_nonneg
                      (by exact_mod_cast Nat.zero_le m) ε)
                  gcongr
            _ ≤ (C * Real.rpow (M : ℝ) ε) ^ 2 := by
                  have hnonneg : 0 ≤ C * Real.rpow (m : ℝ) ε :=
                    mul_nonneg hC.le (Real.rpow_nonneg
                      (by exact_mod_cast Nat.zero_le m) ε)
                  have hnonnegM : 0 ≤ C * Real.rpow (M : ℝ) ε :=
                    mul_nonneg hC.le (Real.rpow_nonneg
                      (by exact_mod_cast Nat.zero_le M) ε)
                  exact (sq_le_sq₀ hnonneg hnonnegM).2
                    (mul_le_mul_of_nonneg_left hpow hC.le)
    _ = (M : ℝ) * (C * Real.rpow (M : ℝ) ε) ^ 2 := by
      simp [Finset.sum_const, Nat.card_Icc]

/-- The sum of two cubic phases factors through the sum of the variables.
This is the divisor identity behind the sharp two-variable sum fiber bound. -/
theorem primeCubic_add_factorization (a b : ℕ) :
    (primeCubic a : ℤ) + primeCubic b =
      ((a : ℤ) + b) *
        (((a : ℤ) + b) ^ 2 - 3 * (a : ℤ) * b - 1) := by
  rw [primeCubic_cast_int, primeCubic_cast_int]
  ring

/-- For a nonzero target, the sum of the two variables divides their cubic
phase sum. -/
theorem sum_variables_dvd_primeCubic_sum (a b : ℕ) :
    a + b ∣ primeCubic a + primeCubic b := by
  apply Int.natCast_dvd_natCast.mp
  push_cast
  rw [primeCubic_add_factorization]
  exact dvd_mul_right _ _

/-- Equal sums and equal cubic-phase sums determine an unordered pair. -/
private theorem primeCubic_pair_eq_or_swap
    {a b c d : ℕ} (hs : 0 < a + b)
    (hsum : a + b = c + d)
    (hphase : primeCubic a + primeCubic b =
      primeCubic c + primeCubic d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hsumZ : (a : ℤ) + b = (c : ℤ) + d := by exact_mod_cast hsum
  have hphaseZ : (primeCubic a : ℤ) + primeCubic b =
      (primeCubic c : ℤ) + primeCubic d := by exact_mod_cast hphase
  rw [primeCubic_add_factorization,
    primeCubic_add_factorization, ← hsumZ] at hphaseZ
  have hleft : (a : ℤ) + b ≠ 0 := by
    have hsZ : (0 : ℤ) < (a : ℤ) + b := by exact_mod_cast hs
    exact hsZ.ne'
  have hquad := mul_left_cancel₀ hleft hphaseZ
  have hprod : (a : ℤ) * b = (c : ℤ) * d := by nlinarith
  have hroot : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    have hid : ((a : ℤ) - c) * ((a : ℤ) - d) =
        (a : ℤ) * ((a : ℤ) + b - c - d) +
          ((c : ℤ) * d - (a : ℤ) * b) := by ring
    rw [hid]
    rw [show (a : ℤ) + b - c - d = 0 by linarith [hsumZ]]
    rw [show (c : ℤ) * d - (a : ℤ) * b = 0 by linarith [hprod]]
    ring
  rcases mul_eq_zero.mp hroot with hac | had
  · left
    have hac' : a = c := by exact_mod_cast sub_eq_zero.mp hac
    exact ⟨hac', by omega⟩
  · right
    have had' : a = d := by exact_mod_cast sub_eq_zero.mp had
    exact ⟨had', by omega⟩

/-- Ordered pairs in the finite interval with a prescribed positive sum of
cubic phases. -/
def positiveCubicPairSumFiber (N t : ℕ) : Finset
    (Fin (N + 1) × Fin (N + 1)) :=
  (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).filter fun ab =>
    primeCubic ab.1.val + primeCubic ab.2.val = t

/-- A positive sum of two cubic phases has at most twice as many ordered
representations as it has divisors. The factor two records pair reversal. -/
theorem card_positiveCubicPairSumFiber_le_twice_divisors
    (N t : ℕ) (ht : 0 < t) :
    (positiveCubicPairSumFiber N t).card ≤ 2 * t.divisors.card := by
  classical
  let encode : (Fin (N + 1) × Fin (N + 1)) → ℕ × Bool :=
    fun ab => (ab.1.val + ab.2.val, decide (ab.1.val ≤ ab.2.val))
  have hcard :
      (positiveCubicPairSumFiber N t).card ≤
        (t.divisors.product (Finset.univ : Finset Bool)).card := by
    refine Finset.card_le_card_of_injOn encode ?_ ?_
    · intro ab hab
      rw [Finset.mem_coe]
      have hphase := (Finset.mem_filter.mp hab).2
      have hdiv : ab.1.val + ab.2.val ∣ t := by
        rw [← hphase]
        exact sum_variables_dvd_primeCubic_sum ab.1.val ab.2.val
      change (ab.1.val + ab.2.val,
        decide (ab.1.val ≤ ab.2.val)) ∈
          t.divisors.product (Finset.univ : Finset Bool)
      exact Finset.mk_mem_product
        (Nat.mem_divisors.mpr ⟨hdiv, ht.ne'⟩) (Finset.mem_univ _)
    · intro ab hab cd hcd heq
      have habphase := (Finset.mem_filter.mp hab).2
      have hcdphase := (Finset.mem_filter.mp hcd).2
      have hsum : ab.1.val + ab.2.val =
          cd.1.val + cd.2.val := (Prod.mk.inj heq).1
      have horient : decide (ab.1.val ≤ ab.2.val) =
          decide (cd.1.val ≤ cd.2.val) := (Prod.mk.inj heq).2
      have hspos : 0 < ab.1.val + ab.2.val := by
        by_contra hnot
        have hz : ab.1.val + ab.2.val = 0 := by omega
        have ha : ab.1.val = 0 := by omega
        have hb : ab.2.val = 0 := by omega
        simp [ha, hb, primeCubic] at habphase
        omega
      rcases primeCubic_pair_eq_or_swap hspos hsum
          (habphase.trans hcdphase.symm) with hsame | hswap
      · apply Prod.ext <;> apply Fin.ext
        · exact hsame.1
        · exact hsame.2
      · have horient' : (ab.1.val ≤ ab.2.val) ↔
            (cd.1.val ≤ cd.2.val) := by
          by_cases h₁ : ab.1.val ≤ ab.2.val <;>
            by_cases h₂ : cd.1.val ≤ cd.2.val <;>
              simp [h₁, h₂] at horient ⊢
        have hsame : ab.1.val = cd.1.val ∧
            ab.2.val = cd.2.val := by omega
        apply Prod.ext <;> apply Fin.ext
        · exact hsame.1
        · exact hsame.2
  simpa [mul_comm] using hcard

private theorem primeCubic_strict_of_pos {a b : ℕ}
    (ha : 0 < a) (hab : a < b) : primeCubic a < primeCubic b := by
  have ha_pow : a ≤ a ^ 3 := Nat.le_pow (by norm_num)
  have hb_pow : b ≤ b ^ 3 := Nat.le_pow (by norm_num)
  have ha_int : ((primeCubic a : ℕ) : ℤ) = (a : ℤ) ^ 3 - a := by
    simp [primeCubic, Nat.cast_sub ha_pow]
  have hb_int : ((primeCubic b : ℕ) : ℤ) = (b : ℤ) ^ 3 - b := by
    simp [primeCubic, Nat.cast_sub hb_pow]
  have hab_int : (a : ℤ) < b := by exact_mod_cast hab
  have ha_int_pos : (0 : ℤ) < a := by exact_mod_cast ha
  have hfactor_pos :
      (0 : ℤ) < ((b : ℤ) - a) *
        ((b : ℤ) ^ 2 + b * a + (a : ℤ) ^ 2 - 1) := by
    have hleft : (0 : ℤ) < (b : ℤ) - a := sub_pos.mpr hab_int
    have hright : (0 : ℤ) <
        (b : ℤ) ^ 2 + b * a + (a : ℤ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((b : ℤ) - 1), sq_nonneg ((a : ℤ) - 1)]
    positivity
  have hpoly : (a : ℤ) ^ 3 - a < (b : ℤ) ^ 3 - b := by
    have hid :
        ((b : ℤ) ^ 3 - b) - ((a : ℤ) ^ 3 - a) =
          ((b : ℤ) - a) *
            ((b : ℤ) ^ 2 + b * a + (a : ℤ) ^ 2 - 1) := by ring
    linarith
  exact_mod_cast (ha_int ▸ hb_int ▸ hpoly)

/-- The cubic phase is injective on the positive natural numbers. -/
theorem primeCubic_injective_of_pos {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (h : primeCubic a = primeCubic b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (ne_of_lt (primeCubic_strict_of_pos ha hab) h).elim
  · exact hab
  · exact (ne_of_gt (primeCubic_strict_of_pos hb hab) h).elim

/-- At zero shift, equality of the two positive cubic phases forces the base
variables to agree; thus the zero-shift fourth-moment contribution is
diagonal. -/
theorem eq_of_zero_shift_cubic_relation {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (heq : (primeCubic a : ℤ) - primeCubic b = 0) : a = b := by
  have hcast : (primeCubic a : ℤ) = primeCubic b := by omega
  exact primeCubic_injective_of_pos ha hb (by exact_mod_cast hcast)

/-- Every value of `x³-x` has at most two preimages in a finite initial
interval.  The only failure of injectivity is `0³-0 = 1³-1`. -/
theorem card_filter_primeCubic_eq_le_two (N t : ℕ) :
    ((Finset.univ : Finset (Fin (N + 1))).filter
      (fun x : Fin (N + 1) ↦ primeCubic x.val = t)).card ≤ 2 := by
  classical
  let z : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  let s : Finset (Fin (N + 1)) :=
    (Finset.univ : Finset (Fin (N + 1))).filter
      (fun x : Fin (N + 1) ↦ primeCubic x.val = t)
  have herase : (s.erase z).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha_mem := Finset.mem_erase.mp ha
    have hb_mem := Finset.mem_erase.mp hb
    apply Fin.ext
    apply primeCubic_injective_of_pos
    · apply Nat.pos_of_ne_zero
      intro ha0
      apply ha_mem.1
      apply Fin.ext
      simpa [z] using ha0
    · apply Nat.pos_of_ne_zero
      intro hb0
      apply hb_mem.1
      apply Fin.ext
      simpa [z] using hb0
    · exact (Finset.mem_filter.mp ha_mem.2).2.trans
        (Finset.mem_filter.mp hb_mem.2).2.symm
  have hcard : s.card ≤ (s.erase z).card + 1 := by
    by_cases hzero : z ∈ s
    · rw [← Finset.card_erase_add_one hzero]
    · rw [Finset.erase_eq_self.mpr hzero]
      omega
  change s.card ≤ 2
  exact hcard.trans (by omega)

/-- The zero-shift contribution is quadratic, not cubic: the equality
`primeCubic a = primeCubic b` has at most two choices of `b` for each `a`,
and the shift variable is then free. -/
theorem cubicZeroFourthShiftCount_le_quadratic (N : ℕ) :
    cubicZeroFourthShiftCount N ≤ 2 * (N + 1) ^ 2 := by
  classical
  let A := Fin (N + 1)
  have hinner (a b : A) :
      (∑ _m : A,
        if primeCubic a.val = primeCubic b.val then 1 else 0) =
        if primeCubic a.val = primeCubic b.val then N + 1 else 0 := by
    split_ifs <;> simp [A]
  have houter (a : A) :
      (∑ b : A,
        if primeCubic a.val = primeCubic b.val then N + 1 else 0) ≤
          2 * (N + 1) := by
    calc
      _ ≤ ∑ b : A,
          (if primeCubic a.val = primeCubic b.val then 1 else 0) *
            (N + 1) := by
        apply Finset.sum_le_sum
        intro b _hb
        split_ifs <;> simp
      _ = (∑ b : A,
          if primeCubic a.val = primeCubic b.val then 1 else 0) *
            (N + 1) := by rw [Finset.sum_mul]
      _ ≤ 2 * (N + 1) := by
        apply Nat.mul_le_mul_right
        simpa [eq_comm] using
          (card_filter_primeCubic_eq_le_two N (primeCubic a.val))
  unfold cubicZeroFourthShiftCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _a : A, 2 * (N + 1) := by
      apply Finset.sum_le_sum
      intro a _ha
      calc
        (∑ b : A,
          ∑ _m : A,
            if primeCubic a.val = primeCubic b.val then 1 else 0) ≤
            ∑ b : A,
              if primeCubic a.val = primeCubic b.val then N + 1 else 0 := by
          apply Finset.sum_le_sum
          intro b _hb
          rw [hinner]
        _ ≤ 2 * (N + 1) := houter a
    _ = 2 * (N + 1) ^ 2 := by simp [A]; ring

/-- The fourth-shift reduction with the zero-shift diagonal counted sharply.
Compared with `cubicFourthShiftCount_le_divisor_sum`, this removes the
spurious large contribution from equal outer phases: their positive-shift
fibers contain at most one exceptional pair in each orientation. -/
theorem cubicFourthShiftCount_le_divisor_sum_sharpZero (N : ℕ) :
    cubicPositiveFourthShiftCount N + cubicZeroFourthShiftCount N ≤
      (∑ ab : Fin (N + 1) × Fin (N + 1),
        if primeCubic ab.1.val ≠ primeCubic ab.2.val then
          2 * ((primeCubic ab.1.val : ℤ) -
            primeCubic ab.2.val).natAbs.divisors.card
        else 2) + 2 * (N + 1) ^ 2 := by
  classical
  let A := Fin (N + 1)
  have hpos : cubicPositiveFourthShiftCount N ≤
      ∑ ab : A × A,
        if primeCubic ab.1.val ≠ primeCubic ab.2.val then
          2 * ((primeCubic ab.1.val : ℤ) -
            primeCubic ab.2.val).natAbs.divisors.card
        else 2 := by
    unfold cubicPositiveFourthShiftCount
    apply Finset.sum_le_sum
    intro ab _hab
    by_cases hneq : primeCubic ab.1.val ≠ primeCubic ab.2.val
    · have hf := card_forwardCubicShiftFiber_le_divisors N
        ab.1.val ab.2.val hneq
      have hb := card_backwardCubicShiftFiber_le_divisors N
        ab.1.val ab.2.val hneq
      simp [hneq]
      omega
    · have heq : primeCubic ab.1.val = primeCubic ab.2.val := by
        by_contra h
        exact hneq h
      have hf := card_forwardCubicShiftFiber_le_one_of_equal_outer
        N ab.1.val ab.2.val heq
      have hb := card_backwardCubicShiftFiber_le_one_of_equal_outer
        N ab.1.val ab.2.val heq
      simp [hneq]
      omega
  unfold cubicPositiveFourthShiftCount cubicZeroFourthShiftCount
  exact Nat.add_le_add hpos (cubicZeroFourthShiftCount_le_quadratic N)

/-- The zero target is exceptional for divisor counting, but it has at most
four ordered two-variable representations: each phase must vanish. -/
theorem card_zeroCubicPairSumFiber_le_four (N : ℕ) :
    (positiveCubicPairSumFiber N 0).card ≤ 4 := by
  classical
  let A := Fin (N + 1)
  let z : Finset A := (Finset.univ : Finset A).filter fun x =>
    primeCubic x.val = 0
  have hsub : positiveCubicPairSumFiber N 0 ⊆ z.product z := by
    intro ab hab
    have hphase := (Finset.mem_filter.mp hab).2
    have ha : primeCubic ab.1.val = 0 := by omega
    have hb : primeCubic ab.2.val = 0 := by omega
    exact Finset.mk_mem_product
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  have hz : z.card ≤ 2 := card_filter_primeCubic_eq_le_two N 0
  calc
    (positiveCubicPairSumFiber N 0).card ≤ (z.product z).card :=
      Finset.card_le_card hsub
    _ = z.card * z.card := Finset.card_product z z
    _ ≤ 4 := by nlinarith

/-- Uniform divisor-fiber bound, including the exceptional zero target.
The upper limit `M` can be chosen independently of the interval length. -/
theorem exists_uniform_cubicPairSumFiber_rpow_bound {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M t : ℕ, 0 < M → t ≤ M →
      ((positiveCubicPairSumFiber N t).card : ℝ) ≤
        4 + 2 * C * Real.rpow (M : ℝ) ε := by
  obtain ⟨C, hC, hbound⟩ := exists_divisor_rpow_bound hε
  refine ⟨C, hC, fun N M t hM htM ↦ ?_⟩
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hpowM : 0 ≤ Real.rpow (M : ℝ) ε :=
    Real.rpow_nonneg hMnonneg ε
  by_cases ht : t = 0
  · subst t
    have hzero := card_zeroCubicPairSumFiber_le_four N
    have hzeroR : ((positiveCubicPairSumFiber N 0).card : ℝ) ≤ 4 := by
      exact_mod_cast hzero
    nlinarith [mul_nonneg hC.le hpowM]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hcard := card_positiveCubicPairSumFiber_le_twice_divisors N t htpos
    have hcardR : ((positiveCubicPairSumFiber N t).card : ℝ) ≤
        2 * (t.divisors.card : ℝ) := by exact_mod_cast hcard
    have hdiv := hbound t ht
    have hpow : Real.rpow (t : ℝ) ε ≤ Real.rpow (M : ℝ) ε := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast htM
      · exact hε.le
    nlinarith [mul_nonneg hC.le (Real.rpow_nonneg
      (by positivity : (0 : ℝ) ≤ t) ε)]

/-- The fourth additive energy of the unweighted cubic phase. -/
def cubicFourthSolutionCount (N : ℕ) : ℕ :=
  ∑ ab : Fin (N + 1) × Fin (N + 1),
    (positiveCubicPairSumFiber N
      (primeCubic ab.1.val + primeCubic ab.2.val)).card

/-- The fourth energy is exactly the number of ordered solutions to
`f(a)+f(b)=f(c)+f(d)`. -/
theorem cubicFourthSolutionCount_eq_indicator (N : ℕ) :
    cubicFourthSolutionCount N =
      ∑ ab : Fin (N + 1) × Fin (N + 1),
        ∑ cd : Fin (N + 1) × Fin (N + 1),
          if primeCubic ab.1.val + primeCubic ab.2.val =
            primeCubic cd.1.val + primeCubic cd.2.val then 1 else 0 := by
  unfold cubicFourthSolutionCount positiveCubicPairSumFiber
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro cd _hcd
  split_ifs <;> simp_all [eq_comm]

/-- Every two-variable cubic-phase sum in the interval lies below twice
the cube of the endpoint. -/
theorem cubicPairSum_fin_le (N : ℕ)
    (ab : Fin (N + 1) × Fin (N + 1)) :
    primeCubic ab.1.val + primeCubic ab.2.val ≤
      2 * (N + 1) ^ 3 := by
  have h₁ : primeCubic ab.1.val ≤ (N + 1) ^ 3 := by
    calc
      _ ≤ ab.1.val ^ 3 := Nat.sub_le _ _
      _ ≤ (N + 1) ^ 3 :=
        Nat.pow_le_pow_left (Nat.le_of_lt ab.1.isLt) 3
  have h₂ : primeCubic ab.2.val ≤ (N + 1) ^ 3 := by
    calc
      _ ≤ ab.2.val ^ 3 := Nat.sub_le _ _
      _ ≤ (N + 1) ^ 3 :=
        Nat.pow_le_pow_left (Nat.le_of_lt ab.2.isLt) 3
  omega

/-- Fourth-moment strength: up to a subpolynomial divisor factor, the
fourth cubic additive energy grows quadratically in the interval length.
This is a genuine input to the later eighth-moment differencing argument. -/
theorem exists_cubicFourthSolutionCount_rpow_bound {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (cubicFourthSolutionCount N : ℝ) ≤
        (N + 1 : ℝ) ^ 2 *
          (4 + 2 * C * Real.rpow (2 * (N + 1 : ℝ) ^ 3) ε) := by
  obtain ⟨C, hC, hfiber⟩ :=
    exists_uniform_cubicPairSumFiber_rpow_bound hε
  refine ⟨C, hC, fun N ↦ ?_⟩
  let M : ℕ := 2 * (N + 1) ^ 3
  have hM : 0 < M := by dsimp [M]; positivity
  have hcastM : (M : ℝ) = 2 * (N + 1 : ℝ) ^ 3 := by
    simp [M]
  have hsum : (cubicFourthSolutionCount N : ℝ) =
      ∑ ab : Fin (N + 1) × Fin (N + 1),
        ((positiveCubicPairSumFiber N
          (primeCubic ab.1.val + primeCubic ab.2.val)).card : ℝ) := by
    simp [cubicFourthSolutionCount]
  rw [hsum]
  calc
    _ ≤ ∑ _ab : Fin (N + 1) × Fin (N + 1),
        (4 + 2 * C * Real.rpow (M : ℝ) ε) := by
      apply Finset.sum_le_sum
      intro ab _hab
      exact hfiber N M _ hM (cubicPairSum_fin_le N ab)
    _ = (N + 1 : ℝ) ^ 2 *
          (4 + 2 * C * Real.rpow (2 * (N + 1 : ℝ) ^ 3) ε) := by
      simp [hcastM, pow_two]
      ring

/-- The standard pairing of four coordinates into two ordered pairs. -/
def Internal.HuaEstimateHelpers.cubicPairAppendEquiv (N : ℕ) :
    ((Fin (N + 1) × Fin (N + 1)) ×
      (Fin (N + 1) × Fin (N + 1))) ≃
        (Fin 4 → Fin (N + 1)) :=
  (Equiv.prodCongr
    (finTwoArrowEquiv (Fin (N + 1))).symm
    (finTwoArrowEquiv (Fin (N + 1))).symm).trans
      (Fin.appendEquiv 2 2)

private theorem cubicFourTupleValue_pairAppend (N : ℕ)
    (ab cd : Fin (N + 1) × Fin (N + 1)) :
    cubicFourTupleValue (Internal.HuaEstimateHelpers.cubicPairAppendEquiv N (ab, cd)) =
      (primeCubic ab.1.val + primeCubic ab.2.val) +
        (primeCubic cd.1.val + primeCubic cd.2.val) := by
  simp [Internal.HuaEstimateHelpers.cubicPairAppendEquiv, cubicFourTupleValue, Fin.sum_univ_four,
    Fin.appendEquiv, Fin.append, Fin.addCases]
  omega

/-- A bound on all two-variable sum fibers bounds each four-variable sum
fiber by the number of choices of its first pair times that bound. -/
theorem sum_fourTuple_indicator_le_of_pairFiber_bound
    (N t B : ℕ)
    (hB : ∀ s : ℕ, s ≤ t →
      (positiveCubicPairSumFiber N s).card ≤ B) :
    (∑ y : Fin 4 → Fin (N + 1),
      if cubicFourTupleValue y = t then 1 else 0) ≤
        (N + 1) ^ 2 * B := by
  classical
  let A := Fin (N + 1)
  let P := A × A
  let e := Internal.HuaEstimateHelpers.cubicPairAppendEquiv N
  let F : (Fin 4 → A) → ℕ := fun y =>
    if cubicFourTupleValue y = t then 1 else 0
  have hinner : ∀ c : ℕ,
      (∑ cd : P,
        if c + (primeCubic cd.1.val + primeCubic cd.2.val) = t then
          1 else 0) ≤ B := by
    intro c
    by_cases hc : c ≤ t
    · have heq :
          (∑ cd : P,
            if c + (primeCubic cd.1.val + primeCubic cd.2.val) = t then
              1 else 0) =
            (positiveCubicPairSumFiber N (t - c)).card := by
        unfold positiveCubicPairSumFiber
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro cd _hcd
        by_cases h : primeCubic cd.1.val + primeCubic cd.2.val = t - c
        · have h' : c + (primeCubic cd.1.val + primeCubic cd.2.val) = t := by
            omega
          simp [h]
          omega
        · have h' : ¬c + (primeCubic cd.1.val + primeCubic cd.2.val) = t := by
            omega
          simp [h, h']
      rw [heq]
      exact hB (t - c) (Nat.sub_le _ _)
    · have hnone : ∀ cd : P,
          ¬ c + (primeCubic cd.1.val + primeCubic cd.2.val) = t := by
        intro cd heq
        omega
      simp [hnone]
  calc
    (∑ y : Fin 4 → A, F y) =
        ∑ z : P × P, F (e z) := (e.sum_comp F).symm
    _ = ∑ ab : P, ∑ cd : P,
          if (primeCubic ab.1.val + primeCubic ab.2.val) +
              (primeCubic cd.1.val + primeCubic cd.2.val) = t then
            1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ab _hab
      apply Finset.sum_congr rfl
      intro cd _hcd
      change (if cubicFourTupleValue (Internal.HuaEstimateHelpers.cubicPairAppendEquiv N (ab, cd)) = t
        then 1 else 0) = _
      rw [cubicFourTupleValue_pairAppend]
    _ ≤ ∑ _ab : P, B := by
      apply Finset.sum_le_sum
      intro ab _hab
      exact hinner _
    _ = (N + 1) ^ 2 * B := by
      simp [P, A, pow_two]

/-- A four-variable cubic-phase value is at most four cubes of the
summation endpoint. -/
theorem cubicFourTupleValue_fin_le (N : ℕ)
    (x : Fin 4 → Fin (N + 1)) :
    cubicFourTupleValue x ≤ 4 * (N + 1) ^ 3 := by
  have hphase (i : Fin 4) : primeCubic (x i).val ≤ (N + 1) ^ 3 := by
    calc
      _ ≤ (x i).val ^ 3 := Nat.sub_le _ _
      _ ≤ (N + 1) ^ 3 :=
        Nat.pow_le_pow_left (Nat.le_of_lt (x i).isLt) 3
  unfold cubicFourTupleValue
  rw [Fin.sum_univ_four]
  nlinarith [hphase 0, hphase 1, hphase 2, hphase 3]

/-- A uniform two-variable fiber bound gives the corresponding eighth-energy
bound by fixing the first four-tuple. -/
theorem cubicEighthSolutionCount_le_of_pairFiber_bound
    (N B : ℕ)
    (hB : ∀ s : ℕ, s ≤ 4 * (N + 1) ^ 3 →
      (positiveCubicPairSumFiber N s).card ≤ B) :
    cubicEighthSolutionCount N ≤ (N + 1) ^ 6 * B := by
  unfold cubicEighthSolutionCount
  calc
    (∑ x : Fin 4 → Fin (N + 1),
      ∑ y : Fin 4 → Fin (N + 1),
        if cubicFourTupleValue x = cubicFourTupleValue y then 1 else 0) ≤
      ∑ _x : Fin 4 → Fin (N + 1), (N + 1) ^ 2 * B := by
        apply Finset.sum_le_sum
        intro x _hx
        simpa only [eq_comm] using
          sum_fourTuple_indicator_le_of_pairFiber_bound
            N (cubicFourTupleValue x) B
              (fun s hs ↦ hB s
                (hs.trans (cubicFourTupleValue_fin_le N x)))
    _ = (N + 1) ^ 6 * B := by
      simp
      ring

/-- The two-variable divisor bound improves the elementary eighth-energy
exponent from seven to six (up to an arbitrarily small extra power). This
does not yet reach Hua's sharp exponent five. -/
theorem exists_cubicEighthSolutionCount_rpow_bound {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (cubicEighthSolutionCount N : ℝ) ≤
        (N + 1 : ℝ) ^ 6 *
          (5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε) := by
  obtain ⟨C, hC, hfiber⟩ :=
    exists_uniform_cubicPairSumFiber_rpow_bound hε
  refine ⟨C, hC, fun N ↦ ?_⟩
  let M : ℕ := 4 * (N + 1) ^ 3
  let D : ℝ := 4 + 2 * C * Real.rpow (M : ℝ) ε
  let B : ℕ := Nat.ceil D
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    have hpow : 0 ≤ Real.rpow (M : ℝ) ε :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le M) ε
    positivity
  have hB : ∀ s : ℕ, s ≤ M →
      (positiveCubicPairSumFiber N s).card ≤ B := by
    intro s hs
    have hreal := hfiber N M s hM hs
    have hceil : ((positiveCubicPairSumFiber N s).card : ℝ) ≤
        (B : ℝ) := hreal.trans (Nat.le_ceil D)
    exact_mod_cast hceil
  have hcount := cubicEighthSolutionCount_le_of_pairFiber_bound N B hB
  have hcountR : (cubicEighthSolutionCount N : ℝ) ≤
      (N + 1 : ℝ) ^ 6 * B := by exact_mod_cast hcount
  have hceil : (B : ℝ) ≤ D + 1 :=
    (Nat.ceil_lt_add_one hD).le
  have hcastM : (M : ℝ) = 4 * (N + 1 : ℝ) ^ 3 := by
    simp [M]
  calc
    (cubicEighthSolutionCount N : ℝ) ≤
        (N + 1 : ℝ) ^ 6 * B := hcountR
    _ ≤ (N + 1 : ℝ) ^ 6 * (D + 1) := by gcongr
    _ = (N + 1 : ℝ) ^ 6 *
          (5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε) := by
      rw [show D + 1 =
          5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε by
        dsimp [D]
        rw [hcastM]
        ring]

/-- Indicator-sum form of the two-point fiber bound. -/
theorem sum_indicator_primeCubic_add_eq_le_two
    (N c t : ℕ) :
    (∑ a : Fin (N + 1), if primeCubic a.val + c = t then 1 else 0) ≤ 2 := by
  classical
  rw [← Finset.card_filter]
  change ((Finset.univ : Finset (Fin (N + 1))).filter
    (fun a : Fin (N + 1) ↦ primeCubic a.val + c = t)).card ≤ 2
  by_cases hct : c ≤ t
  · have hs : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun a : Fin (N + 1) ↦ primeCubic a.val + c = t) =
      (Finset.univ : Finset (Fin (N + 1))).filter
        (fun a : Fin (N + 1) ↦ primeCubic a.val = t - c) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hs]
    exact card_filter_primeCubic_eq_le_two N (t - c)
  · have hs : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun a : Fin (N + 1) ↦ primeCubic a.val + c = t) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro heq
        have htc : t < c := Nat.lt_of_not_ge hct
        have hlt : t < primeCubic a.val + c :=
          htc.trans_le (Nat.le_add_left c (primeCubic a.val))
        exact ((ne_of_gt hlt) heq).elim
      · intro hempty
        simp at hempty
    rw [hs]
    simp

private theorem cubicFourTupleValue_insert_zero
    {N : ℕ} (a : Fin (N + 1)) (y : Fin 3 → Fin (N + 1)) :
    cubicFourTupleValue
        (Fin.insertNth (0 : Fin 4) a y : Fin 4 → Fin (N + 1)) =
      primeCubic a.val + ∑ j, primeCubic (y j).val := by
  unfold cubicFourTupleValue
  rw [Fin.sum_univ_succAbove _ (0 : Fin 4)]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- Once three coordinates are fixed, the fourth coordinate has at most
two possible values. -/
theorem sum_fourTuple_indicator_eq_le (N t : ℕ) :
    (∑ y : Fin 4 → Fin (N + 1),
      if cubicFourTupleValue y = t then 1 else 0) ≤
        2 * (N + 1) ^ 3 := by
  classical
  let A := Fin (N + 1)
  let e : A × (Fin 3 → A) ≃ (Fin 4 → A) :=
    Fin.insertNthEquiv (fun _ : Fin 4 ↦ A) 0
  let F : (Fin 4 → A) → ℕ := fun y ↦
    if cubicFourTupleValue y = t then 1 else 0
  calc
    (∑ y : Fin 4 → A, F y) = ∑ z : A × (Fin 3 → A), F (e z) :=
      (e.sum_comp F).symm
    _ = ∑ y : Fin 3 → A, ∑ a : A,
        if primeCubic a.val + ∑ j, primeCubic (y j).val = t then
          1 else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro a _ha
      rw [show e (a, y) =
          (Fin.insertNth (0 : Fin 4) a y : Fin 4 → A) from rfl]
      simp only [F, cubicFourTupleValue_insert_zero]
    _ ≤ ∑ _y : Fin 3 → A, 2 := by
      exact Finset.sum_le_sum fun y _hy ↦
        sum_indicator_primeCubic_add_eq_le_two N
          (∑ j, primeCubic (y j).val) t
    _ = 2 * (N + 1) ^ 3 := by
      simp [A, mul_comm]

/-- Elementary unweighted eighth-energy bound obtained by fixing the first
four-tuple and three entries of the second. -/
theorem cubicEighthSolutionCount_le (N : ℕ) :
    cubicEighthSolutionCount N ≤ 2 * (N + 1) ^ 7 := by
  unfold cubicEighthSolutionCount
  calc
    (∑ x : Fin 4 → Fin (N + 1),
        ∑ y : Fin 4 → Fin (N + 1),
          if cubicFourTupleValue x = cubicFourTupleValue y then 1 else 0) ≤
      ∑ _x : Fin 4 → Fin (N + 1), 2 * (N + 1) ^ 3 := by
        apply Finset.sum_le_sum
        intro x _hx
        simpa only [eq_comm] using
          sum_fourTuple_indicator_eq_le N (cubicFourTupleValue x)
    _ = 2 * (N + 1) ^ 7 := by
      simp
      ring

/-- A uniform upper bound for each von--Mangoldt weight in the finite
summation interval. -/
theorem vonMangoldt_fin_le_log_succ {N : ℕ} (x : Fin (N + 1)) :
    ArithmeticFunction.vonMangoldt x.val ≤ Real.log (N + 1 : ℝ) := by
  by_cases hx : x.val = 0
  · rw [hx]
    rw [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  · calc
      ArithmeticFunction.vonMangoldt x.val ≤ Real.log (x.val : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (N + 1 : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast Nat.pos_of_ne_zero hx
        · exact_mod_cast x.isLt.le

theorem log_succ_nonneg (N : ℕ) : 0 ≤ Real.log (N + 1 : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))

/-- Each four-tuple weight is bounded by four powers of the endpoint
logarithm. -/
theorem cubicFourTupleWeight_le_log_pow_four {N : ℕ}
    (x : Fin 4 → Fin (N + 1)) :
    cubicFourTupleWeight x ≤ Real.log (N + 1 : ℝ) ^ 4 := by
  unfold cubicFourTupleWeight
  calc
    (∏ i, ArithmeticFunction.vonMangoldt (x i).val) ≤
        ∏ _i : Fin 4, Real.log (N + 1 : ℝ) := by
      exact Finset.prod_le_prod₀
        (fun i _hi ↦ ArithmeticFunction.vonMangoldt_nonneg)
        (fun i _hi ↦ vonMangoldt_fin_le_log_succ (x i))
    _ = Real.log (N + 1 : ℝ) ^ 4 := by simp

theorem cubicFourTupleWeight_nonneg {N : ℕ}
    (x : Fin 4 → Fin (N + 1)) : 0 ≤ cubicFourTupleWeight x := by
  unfold cubicFourTupleWeight
  exact Finset.prod_nonneg fun i _hi ↦
    ArithmeticFunction.vonMangoldt_nonneg

/-- Removing all von--Mangoldt weights costs at most eight endpoint
logarithms. -/
theorem cubicVonMangoldtEighthEnergy_le_count (N : ℕ) :
    cubicVonMangoldtEighthEnergy N ≤
      Real.log (N + 1 : ℝ) ^ 8 * cubicEighthSolutionCount N := by
  have hcount_cast : ((cubicEighthSolutionCount N : ℕ) : ℝ) =
      ∑ x : Fin 4 → Fin (N + 1), ∑ y : Fin 4 → Fin (N + 1),
        if cubicFourTupleValue x = cubicFourTupleValue y then (1 : ℝ) else 0 := by
    unfold cubicEighthSolutionCount
    push_cast
    rfl
  rw [hcount_cast, Finset.mul_sum]
  unfold cubicVonMangoldtEighthEnergy
  apply Finset.sum_le_sum
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _hy
  by_cases hxy : cubicFourTupleValue x = cubicFourTupleValue y
  · simp only [hxy, ite_true, mul_one]
    have hxw := cubicFourTupleWeight_le_log_pow_four x
    have hyw := cubicFourTupleWeight_le_log_pow_four y
    calc
      cubicFourTupleWeight x * cubicFourTupleWeight y ≤
          Real.log (N + 1 : ℝ) ^ 4 *
            Real.log (N + 1 : ℝ) ^ 4 := by
        exact mul_le_mul hxw hyw (cubicFourTupleWeight_nonneg y)
          (pow_nonneg (log_succ_nonneg N) 4)
      _ = Real.log (N + 1 : ℝ) ^ 8 := by ring
  · simp [hxy]

/-- Weighted eighth-moment bound of exponent `6+ε`, using the two-variable
sum-fiber divisor estimate. The remaining sharp Hua step must save one
further power of the interval length. -/
theorem exists_cubicVonMangoldtEighthMoment_rpow_bound {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      cubicVonMangoldtEighthMoment N ≤
        Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 6 *
          (5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_cubicEighthSolutionCount_rpow_bound hε
  refine ⟨C, hC, fun N ↦ ?_⟩
  rw [cubicVonMangoldtEighthMoment_eq_energy]
  calc
    cubicVonMangoldtEighthEnergy N ≤
        Real.log (N + 1 : ℝ) ^ 8 * cubicEighthSolutionCount N :=
      cubicVonMangoldtEighthEnergy_le_count N
    _ ≤ Real.log (N + 1 : ℝ) ^ 8 *
          ((N + 1 : ℝ) ^ 6 *
            (5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε)) := by
      exact mul_le_mul_of_nonneg_left (hcount N)
        (pow_nonneg (log_succ_nonneg N) 8)
    _ = Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 6 *
          (5 + 2 * C * Real.rpow (4 * (N + 1 : ℝ) ^ 3) ε) := by
      ring

/-- Concrete unconditional eighth-moment bound. -/
theorem cubicVonMangoldtEighthMoment_le (N : ℕ) :
    cubicVonMangoldtEighthMoment N ≤
      2 * Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 7 := by
  rw [cubicVonMangoldtEighthMoment_eq_energy]
  calc
    cubicVonMangoldtEighthEnergy N ≤
        Real.log (N + 1 : ℝ) ^ 8 * cubicEighthSolutionCount N :=
      cubicVonMangoldtEighthEnergy_le_count N
    _ ≤ Real.log (N + 1 : ℝ) ^ 8 * (2 * (N + 1) ^ 7) := by
      gcongr
      exact_mod_cast cubicEighthSolutionCount_le N
    _ = 2 * Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 7 := by
      ring

/-- The elementary scale delivered by the finite-fiber argument. -/
noncomputable def cubicElementaryHuaScale (N : ℕ) : ℝ :=
  Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 7

theorem cubicVonMangoldtEighthMoment_nonneg (N : ℕ) :
    0 ≤ cubicVonMangoldtEighthMoment N := by
  unfold cubicVonMangoldtEighthMoment
  exact integral_nonneg fun _ ↦ by positivity

theorem cubicElementaryHuaScale_nonneg (N : ℕ) :
    0 ≤ cubicElementaryHuaScale N := by
  unfold cubicElementaryHuaScale
  positivity

/-- Assumption-free asymptotic form of the elementary Hua bound. -/
theorem cubicVonMangoldtEighthMoment_isBigO_elementary :
    (fun N : ℕ ↦ cubicVonMangoldtEighthMoment N) =O[atTop]
      cubicElementaryHuaScale := by
  apply IsBigO.of_bound 2
  filter_upwards [] with N
  rw [Real.norm_eq_abs,
    abs_of_nonneg (cubicVonMangoldtEighthMoment_nonneg N),
    Real.norm_eq_abs, abs_of_nonneg (cubicElementaryHuaScale_nonneg N)]
  simpa only [cubicElementaryHuaScale, mul_assoc] using
    cubicVonMangoldtEighthMoment_le N

/-- Exact reformulation of the analytic input as a weighted solution-count
estimate. -/
theorem cubicHuaEstimate_iff_weightedEnergy :
    CubicHuaEstimate ↔
      (fun N : ℕ ↦ cubicVonMangoldtEighthEnergy N) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ 5 * Real.sqrt N) := by
  unfold CubicHuaEstimate
  have heq : (fun N : ℕ ↦ cubicVonMangoldtEighthMoment N) =
      fun N : ℕ ↦ cubicVonMangoldtEighthEnergy N := by
    funext N
    exact cubicVonMangoldtEighthMoment_eq_energy N
  rw [heq]

/-- The unweighted counting scale to which the exact orthogonality identity
reduces Hua's estimate. -/
noncomputable def cubicUnweightedHuaScale (N : ℕ) : ℝ :=
  Real.log (N + 1 : ℝ) ^ 8 * cubicEighthSolutionCount N

/-- The precise remaining unweighted counting statement. -/
def CubicUnweightedHuaEstimate : Prop :=
  cubicUnweightedHuaScale =o[atTop]
    (fun N : ℕ ↦ (N : ℝ) ^ 5 * Real.sqrt N)

theorem cubicUnweightedHuaScale_nonneg (N : ℕ) :
    0 ≤ cubicUnweightedHuaScale N := by
  unfold cubicUnweightedHuaScale
  positivity

theorem cubicVonMangoldtEighthEnergy_isBigO_unweighted :
    (fun N : ℕ ↦ cubicVonMangoldtEighthEnergy N) =O[atTop]
      cubicUnweightedHuaScale := by
  apply isBigO_of_le
  intro N
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by
      rw [← cubicVonMangoldtEighthMoment_eq_energy]
      exact cubicVonMangoldtEighthMoment_nonneg N),
    Real.norm_eq_abs, abs_of_nonneg (cubicUnweightedHuaScale_nonneg N)]
  exact cubicVonMangoldtEighthEnergy_le_count N

/-- An unweighted `5+ε`-strength solution-count estimate would complete the
Hua input with no further analytic bookkeeping. -/
theorem CubicUnweightedHuaEstimate.toCubicHuaEstimate
    (h : CubicUnweightedHuaEstimate) : CubicHuaEstimate := by
  rw [cubicHuaEstimate_iff_weightedEnergy]
  exact cubicVonMangoldtEighthEnergy_isBigO_unweighted.trans_isLittleO h

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.cubicZeroFourthShiftCount_le_quadratic
#print axioms SystolicGrowth.CookMagyarCircle.cubicFourthShiftCount_le_divisor_sum_sharpZero
#print axioms SystolicGrowth.CookMagyarCircle.card_positiveCubicThirdDifferenceShiftFiber_le_divisors_sq
#print axioms SystolicGrowth.CookMagyarCircle.natAbs_primeCubicThirdDifference
#print axioms SystolicGrowth.CookMagyarCircle.exists_positiveCubicThirdDifferenceShiftFiber_rpow_bound
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_positiveCubicThirdDifferenceShiftFiber_rpow_bound
#print axioms SystolicGrowth.CookMagyarCircle.card_positiveCubicSecondDifferenceFiber_le_divisors_sq
#print axioms SystolicGrowth.CookMagyarCircle.sum_card_positiveCubicSecondDifferenceFiber_le_cube
#print axioms SystolicGrowth.CookMagyarCircle.exists_cubicSecondDifferenceCoefficientEnergy_bound
#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicSecondDifferenceTripleSum_sq
#print axioms SystolicGrowth.CookMagyarCircle.exists_cubicSecondDifferenceTripleSum_energy_bound
