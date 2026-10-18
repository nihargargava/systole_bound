module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIExceptionalFrequency
public import CookMagyar.OrdinaryWeylSpacing

@[expose] public section

/-!
# The full cubic Type-II five-shift frequency envelope

The divisor-rich tuples are controlled by Hua's unweighted divisor moment.
The remaining tuples are grouped by the exact frequency divided by six,
then bounded by the sixfold rational-spacing estimate. The tenth moment
gives the fifth-power threshold saving needed by the fixed minor-arc gates.
-/

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs

/-- The spacing index retains one factor `3!`; its sixfold multiple is
the full cubic five-shift frequency. -/
def huaTypeIICubicSpacingIndex (l : ℕ) (x : HuaTypeIICubicShifts) : ℕ :=
  6 * l ^ 3 * x.1 * x.2.1 * x.2.2.1 * x.2.2.2.1 * x.2.2.2.2

theorem hua_typeII_cubic_shift_frequency_eq_six_spacing_index
    (l : ℕ) (x : HuaTypeIICubicShifts) :
    huaTypeIICubicShiftFrequency l x = 6 * huaTypeIICubicSpacingIndex l x := by
  dsimp [huaTypeIICubicShiftFrequency, huaTypeIICubicSpacingIndex]
  ring

/-- The spacing indices of the positive shift box lie in its exact product
cutoff, without padding any of the five shift ranges. -/
theorem hua_typeII_cubic_spacing_index_bounds
    (l D P₀ : ℕ) (hl : 0 < l) {x : HuaTypeIICubicShifts}
    (hx : x ∈ huaTypeIICubicShiftBox D P₀) :
    0 < huaTypeIICubicSpacingIndex l x ∧
      huaTypeIICubicSpacingIndex l x ≤ 6 * l ^ 3 * D ^ 3 * P₀ ^ 2 := by
  obtain ⟨hpos, hupper⟩ := hua_typeII_cubic_shift_frequency_bounds l D P₀ hl hx
  rw [hua_typeII_cubic_shift_frequency_eq_six_spacing_index] at hpos hupper
  have hcutoff : 36 * l ^ 3 * D ^ 3 * P₀ ^ 2 =
      6 * (6 * l ^ 3 * D ^ 3 * P₀ ^ 2) := by ring
  rw [hcutoff] at hupper
  omega

/-- The fifth-power fiber cost permits any divisor moment of order at
least five. For moment ten the rich-tuple threshold saving is `T⁻⁵`. -/
theorem hua_typeII_cubic_divisor_rich_shift_count_moment_le
    (l D P₀ M k : ℕ) (hl : 0 < l)
    (hM : 36 * l ^ 3 * D ^ 3 * P₀ ^ 2 ≤ M) (hk : 5 ≤ k)
    (T : ℝ) (hT : 0 ≤ T) :
    T ^ (k - 5) * (((huaTypeIICubicShiftBox D P₀).filter
      (fun x => T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))).card : ℝ) ≤
        (M : ℝ) * (1 + Real.log (M : ℝ)) ^ (2 ^ k - 1) := by
  classical
  let E := (huaTypeIICubicShiftBox D P₀).filter
    (fun x => T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))
  let I := Finset.Icc 1 M
  have hmaps : ∀ x ∈ E, huaTypeIICubicShiftFrequency l x ∈ I := by
    intro x hx
    obtain ⟨hpos, hupper⟩ := hua_typeII_cubic_shift_frequency_bounds l D P₀ hl
      (Finset.mem_filter.mp hx).1
    exact Finset.mem_Icc.mpr ⟨hpos, hupper.trans hM⟩
  have hgroup : (E.card : ℝ) =
      ∑ z ∈ I, ((E.filter
        (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hpoint : ∀ z ∈ I,
      T ^ (k - 5) * ((E.filter
        (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) ≤
          (z.divisors.card : ℝ) ^ k := by
    intro z hzI
    have hz : 0 < z := (Finset.mem_Icc.mp hzI).1
    by_cases hrich : T ≤ (z.divisors.card : ℝ)
    · have hsubset : E.filter (fun x => huaTypeIICubicShiftFrequency l x = z) ⊆
          (huaTypeIICubicShiftBox D P₀).filter
            (fun x => huaTypeIICubicShiftFrequency l x = z) := by
        intro x hx
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩
      have hcard : ((E.filter
          (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) ≤
          (z.divisors.card : ℝ) ^ 5 := by
        exact_mod_cast (Finset.card_le_card hsubset).trans
          (card_hua_typeII_cubic_shift_frequency_fiber_le l D P₀ z hz)
      calc
        _ ≤ (z.divisors.card : ℝ) ^ (k - 5) * (z.divisors.card : ℝ) ^ 5 := by
          exact mul_le_mul (pow_le_pow_left₀ hT hrich _) hcard
            (by positivity) (by positivity)
        _ = (z.divisors.card : ℝ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
    · have hempty : E.filter
          (fun x => huaTypeIICubicShiftFrequency l x = z) = ∅ := by
        ext x
        constructor
        · intro hx
          have hxE := (Finset.mem_filter.mp hx).1
          have hxFreq := (Finset.mem_filter.mp hx).2
          have hxRich := (Finset.mem_filter.mp hxE).2
          exact False.elim (hrich (by simpa [hxFreq] using hxRich))
        · intro hx
          simp at hx
      simp [hempty]
  calc
    T ^ (k - 5) * (E.card : ℝ) =
        ∑ z ∈ I, T ^ (k - 5) * ((E.filter
          (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) := by
      rw [hgroup, Finset.mul_sum]
    _ ≤ ∑ z ∈ I, (z.divisors.card : ℝ) ^ k := Finset.sum_le_sum hpoint
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ (2 ^ k - 1) := by
      simpa [I, divisorUnweightedMoment] using divisorUnweightedMoment_le_envelope M k

/-- The full weighted five-shift envelope, using the tenth divisor moment
for rich tuples and exact reduced-denominator spacing for regular tuples.
The quotient in the number of spacing blocks is natural-number division. -/
theorem hua_typeII_cubic_full_frequency_envelope_le
    (l D P₀ a q : ℕ) (Y T : ℝ)
    (hl : 0 < l) (hq : 0 < q) (hac : Nat.Coprime a q)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) :
    let M : ℕ := 36 * l ^ 3 * D ^ 3 * P₀ ^ 2
    let M₀ : ℕ := 6 * l ^ 3 * D ^ 3 * P₀ ^ 2
    let q₀ : ℕ := q / Nat.gcd q 6
    T ^ 5 * (∑ x ∈ huaTypeIICubicShiftBox D P₀,
      linearDistanceEnvelope Y ((a : ℝ) / q * (huaTypeIICubicShiftFrequency l x : ℝ))) ≤
      Y * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 +
        T ^ 10 * (((M₀ + 1) / q₀ + 1 : ℕ) : ℝ) *
          (28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ)))) := by
  classical
  dsimp only
  let M : ℕ := 36 * l ^ 3 * D ^ 3 * P₀ ^ 2
  let M₀ : ℕ := 6 * l ^ 3 * D ^ 3 * P₀ ^ 2
  let q₀ : ℕ := q / Nat.gcd q 6
  let B := huaTypeIICubicShiftBox D P₀
  let E := B.filter
    (fun x => T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))
  let F := B.filter
    (fun x => ¬ T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))
  let alpha := (a : ℝ) / q
  let w := fun x : HuaTypeIICubicShifts =>
    linearDistanceEnvelope Y (alpha * (huaTypeIICubicShiftFrequency l x : ℝ))
  let f := fun m : ℕ => linearDistanceEnvelope Y ((6 * alpha) * (m : ℝ))
  let I := Finset.Icc 1 M₀
  let C := (((M₀ + 1) / q₀ + 1 : ℕ) : ℝ) *
    (28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))))
  have hweight (x : HuaTypeIICubicShifts) : w x = f (huaTypeIICubicSpacingIndex l x) := by
    dsimp [w, f]
    congr 1
    rw [hua_typeII_cubic_shift_frequency_eq_six_spacing_index, Nat.cast_mul]
    norm_num
    ring
  have hrich : T ^ 5 * (∑ x ∈ E, w x) ≤
      Y * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 := by
    have hsum : (∑ x ∈ E, w x) ≤ (E.card : ℝ) * Y := by
      calc
        _ ≤ ∑ x ∈ E, Y := Finset.sum_le_sum (by
          intro x hx
          exact linearDistanceEnvelope_le Y _)
        _ = (E.card : ℝ) * Y := by simp
    have hcount : T ^ 5 * (E.card : ℝ) ≤
        (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 := by
      simpa [E, B] using hua_typeII_cubic_divisor_rich_shift_count_moment_le
        l D P₀ M 10 hl (by rfl) (by norm_num) T hT
    calc
      _ ≤ T ^ 5 * ((E.card : ℝ) * Y) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Y * (T ^ 5 * (E.card : ℝ)) := by ring
      _ ≤ Y * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023) :=
        mul_le_mul_of_nonneg_left hcount hY
      _ = _ := by rw [mul_assoc]
  have hmaps : ∀ x ∈ F, huaTypeIICubicSpacingIndex l x ∈ I := by
    intro x hx
    obtain ⟨hpos, hupper⟩ := hua_typeII_cubic_spacing_index_bounds l D P₀ hl
      (Finset.mem_filter.mp hx).1
    exact Finset.mem_Icc.mpr ⟨hpos, hupper⟩
  have hcard : ∀ m ∈ I,
      ((F.filter (fun x => huaTypeIICubicSpacingIndex l x = m)).card : ℝ) ≤ T ^ 5 := by
    intro m hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    by_cases hregular : ((6 * m).divisors.card : ℝ) < T
    · have hsubset : F.filter (fun x => huaTypeIICubicSpacingIndex l x = m) ⊆
          B.filter (fun x => huaTypeIICubicShiftFrequency l x = 6 * m) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, ?_⟩
        rw [hua_typeII_cubic_shift_frequency_eq_six_spacing_index,
          (Finset.mem_filter.mp hx).2]
      have hfiber : ((F.filter
          (fun x => huaTypeIICubicSpacingIndex l x = m)).card : ℝ) ≤
          ((6 * m).divisors.card : ℝ) ^ 5 := by
        exact_mod_cast (Finset.card_le_card hsubset).trans
          (card_hua_typeII_cubic_shift_frequency_fiber_le l D P₀ (6 * m) (by omega))
      exact hfiber.trans (pow_le_pow_left₀ (by positivity) hregular.le 5)
    · have hempty : F.filter (fun x => huaTypeIICubicSpacingIndex l x = m) = ∅ := by
        ext x
        constructor
        · intro hx
          have hxF := (Finset.mem_filter.mp hx).1
          have hxIndex := (Finset.mem_filter.mp hx).2
          have hxRegular := (Finset.mem_filter.mp hxF).2
          have hxFreq : huaTypeIICubicShiftFrequency l x = 6 * m := by
            rw [hua_typeII_cubic_shift_frequency_eq_six_spacing_index, hxIndex]
          exact False.elim (hregular (lt_of_not_ge (by simpa [hxFreq] using hxRegular)))
        · intro hx
          simp at hx
      simp [hempty, pow_nonneg hT]
  have hgroup : (∑ x ∈ F, w x) =
      ∑ m ∈ I, ((F.filter
        (fun x => huaTypeIICubicSpacingIndex l x = m)).card : ℝ) * f m := by
    calc
      _ = ∑ x ∈ F, f (huaTypeIICubicSpacingIndex l x) :=
        Finset.sum_congr rfl (by intro x hx; exact hweight x)
      _ = ∑ m ∈ I, ∑ x ∈ F with huaTypeIICubicSpacingIndex l x = m, f m :=
        (Finset.sum_fiberwise_of_maps_to' hmaps f).symm
      _ = _ := by simp
  have hspacing : (∑ m ∈ Finset.range (M₀ + 1), f m) ≤ C := by
    simpa [f, C, q₀] using sum_sixMul_linearDistanceEnvelope_range_le
      (a := a) (q := q) (B := 0) (R := M₀ + 1)
      (alpha := alpha) (beta := 0) Y hq hac
      (by simp [alpha, rationalCenter]) (by simp only [abs_zero]; positivity) hY
  have hregular : T ^ 5 * (∑ x ∈ F, w x) ≤ T ^ 10 * C := by
    have hsum : (∑ x ∈ F, w x) ≤ T ^ 5 * C := by
      calc
        _ = ∑ m ∈ I, ((F.filter
            (fun x => huaTypeIICubicSpacingIndex l x = m)).card : ℝ) * f m := hgroup
        _ ≤ ∑ m ∈ I, T ^ 5 * f m := Finset.sum_le_sum (by
          intro m hm
          exact mul_le_mul_of_nonneg_right (hcard m hm) (linearDistanceEnvelope_nonneg hY))
        _ = T ^ 5 * (∑ m ∈ I, f m) := by rw [Finset.mul_sum]
        _ ≤ T ^ 5 * (∑ m ∈ Finset.range (M₀ + 1), f m) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hm).2; omega)
          · intro m hm hnot
            exact linearDistanceEnvelope_nonneg hY
        _ ≤ T ^ 5 * C := mul_le_mul_of_nonneg_left hspacing (by positivity)
    calc
      _ ≤ T ^ 5 * (T ^ 5 * C) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = T ^ 10 * C := by rw [← mul_assoc, ← pow_add]
  have hsplit : (∑ x ∈ E, w x) + (∑ x ∈ F, w x) = ∑ x ∈ B, w x := by
    exact Finset.sum_filter_add_sum_filter_not B _ w
  have htotal : T ^ 5 * (∑ x ∈ B, w x) ≤
      Y * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 + T ^ 10 * C := by
    rw [← hsplit, mul_add]
    exact add_le_add hrich hregular
  calc
    _ ≤ Y * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 + T ^ 10 * C := htotal
    _ = _ := by
      dsimp only [C]
      rw [mul_assoc (T ^ 10)]

#print axioms hua_typeII_cubic_shift_frequency_eq_six_spacing_index
#print axioms hua_typeII_cubic_spacing_index_bounds
#print axioms hua_typeII_cubic_divisor_rich_shift_count_moment_le
#print axioms hua_typeII_cubic_full_frequency_envelope_le

/-- The actual clipped endpoint bounds the full frequency cutoff by a
constant times `P³`. In particular its logarithm introduces no extra
dependence on the dyadic block or the auxiliary factor. -/
theorem hua_typeII_cubic_frequency_cutoff_le_cube
    (P l D N : ℕ) (hl : 0 < l) (hD : 0 < D) (hN : 0 < N)
    (hNupper : (N : ℝ) ≤ ((P : ℝ) / l) / D) :
    (36 * l ^ 3 * D ^ 3 * N ^ 2 : ℕ) ≤ 36 * P ^ 3 := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbudget : (l : ℝ) * D * N ≤ P := by
    have h := (le_div_iff₀ hlR).mp ((le_div_iff₀ hDR).mp hNupper)
    nlinarith only [h]
  have hbase : (l : ℝ) * D ≤ P := by
    calc
      (l : ℝ) * D = (l : ℝ) * D * 1 := by ring
      _ ≤ (l : ℝ) * D * N := mul_le_mul_of_nonneg_left hNR (by positivity)
      _ ≤ P := hbudget
  have hreal : 36 * (l : ℝ) ^ 3 * (D : ℝ) ^ 3 * (N : ℝ) ^ 2 ≤
      36 * (P : ℝ) ^ 3 := by
    calc
      _ = 36 * ((l : ℝ) * D) * ((l : ℝ) * D * N) ^ 2 := by ring
      _ ≤ 36 * (P : ℝ) * (P : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  exact_mod_cast hreal

#print axioms hua_typeII_cubic_frequency_cutoff_le_cube

/-- A uniform logarithmic envelope for the actual positive frequency
cutoff. Specializing `k = 1023` controls the tenth-moment rich branch. -/
theorem hua_typeII_cubic_frequency_log_envelope_le
    (P l D N k : ℕ) (hl : 0 < l) (hD : 0 < D) (hN : 0 < N)
    (hNupper : (N : ℝ) ≤ ((P : ℝ) / l) / D)
    (hlog : 1 ≤ Real.log (P : ℝ)) :
    (1 + Real.log ((36 * l ^ 3 * D ^ 3 * N ^ 2 : ℕ) : ℝ)) ^ k ≤
      (4 + Real.log 36) ^ k * Real.log (P : ℝ) ^ k := by
  let M := 36 * l ^ 3 * D ^ 3 * N ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcube := hua_typeII_cubic_frequency_cutoff_le_cube P l D N hl hD hN hNupper
  have hP : 0 < P := by
    by_contra h
    have hPzero : P = 0 := by omega
    have hzero : M ≤ 0 := by simpa [M, hPzero] using hcube
    omega
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hcubeR : (M : ℝ) ≤ 36 * (P : ℝ) ^ 3 := by exact_mod_cast hcube
  have hlogM : Real.log (M : ℝ) ≤ Real.log 36 + 3 * Real.log (P : ℝ) := by
    have h := Real.log_le_log hMR hcubeR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    exact h
  have hlog36 : 0 ≤ Real.log (36 : ℝ) := Real.log_nonneg (by norm_num)
  have hbase : 1 + Real.log (M : ℝ) ≤
      (4 + Real.log 36) * Real.log (P : ℝ) := by nlinarith
  have hleft : 0 ≤ 1 + Real.log (M : ℝ) :=
    add_nonneg (by norm_num) (Real.log_nonneg hMone)
  calc
    (1 + Real.log (M : ℝ)) ^ k ≤
        ((4 + Real.log 36) * Real.log (P : ℝ)) ^ k :=
      pow_le_pow_left₀ hleft hbase k
    _ = _ := mul_pow _ _ _

#print axioms hua_typeII_cubic_frequency_log_envelope_le

/-- An integer-power threshold fits the unchanged Type-II logarithmic
gates, including the fifth-power rich tail from the tenth divisor moment. -/
theorem hua_typeII_divisor_threshold_exponent_budget
    (saving sigma3 sigma6 sigma : ℕ)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma) :
    let tau := (3 * sigma3 + 64 * saving + 2052) / 5
    3 * sigma3 + 1023 + 64 * saving < 5 * tau ∧
      5 * tau + 4 * sigma3 + 1 + 64 * saving < sigma6 ∧
      5 * tau + 3 * sigma3 + 1 + 64 * saving < sigma := by
  dsimp only
  omega

#print axioms hua_typeII_divisor_threshold_exponent_budget

end SystolicGrowth.CookMagyarCircle
