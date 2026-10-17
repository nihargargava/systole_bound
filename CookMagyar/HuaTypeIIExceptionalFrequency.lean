module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIFrequency
public import CookMagyar.HuaDivisorBound

@[expose] public section

/-!
# Cubic Type-II exceptional-frequency multiplicity

Hua's Lemma 6.3, printed pp. 71--72, applies three differencing shifts
`ξ₁, ξ₂, ξ₃` and two further shifts `η₁, η₂`. For cubic degree, the
nonzero frequency is `3!² * l³ * ξ₁ ξ₂ ξ₃ η₁ η₂`. The proof bounds the
number of tuples producing one such frequency by the fifth power of its
divisor count. This file formalizes that exact arithmetic constituent.
It supplies no differencing inequality or bound for the regular frequencies.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- The five positive shifts in Hua's cubic Type-II differencing step. -/
abbrev HuaTypeIICubicShifts := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

/-- The source's finite shift box: three shifts at most `D` and two at
most `P₀`. -/
def huaTypeIICubicShiftBox (D P₀ : ℕ) : Finset HuaTypeIICubicShifts :=
  let I := Finset.Icc 1 D
  let J := Finset.Icc 1 P₀
  I.product (I.product (I.product (J.product J)))

/-- For degree three, `3!² = 36` in Hua's post-differencing frequency. -/
def huaTypeIICubicShiftFrequency (l : ℕ) (x : HuaTypeIICubicShifts) : ℕ :=
  36 * l ^ 3 * x.1 * x.2.1 * x.2.2.1 * x.2.2.2.1 * x.2.2.2.2

/-- The positive shifts keep the cubic frequency nonzero and within the
source's product cutoff `36*l³*D³*P₀²`. -/
theorem hua_typeII_cubic_shift_frequency_bounds
    (l D P₀ : ℕ) (hl : 0 < l) {x : HuaTypeIICubicShifts}
    (hx : x ∈ huaTypeIICubicShiftBox D P₀) :
    0 < huaTypeIICubicShiftFrequency l x ∧
      huaTypeIICubicShiftFrequency l x ≤ 36 * l ^ 3 * D ^ 3 * P₀ ^ 2 := by
  rcases x with ⟨ξ₁, ξ₂, ξ₃, η₁, η₂⟩
  simp [huaTypeIICubicShiftBox] at hx
  rcases hx with ⟨⟨hξ₁, hξ₁D⟩, ⟨hξ₂, hξ₂D⟩,
    ⟨hξ₃, hξ₃D⟩, ⟨hη₁, hη₁P⟩, hη₂, hη₂P⟩
  constructor
  · dsimp [huaTypeIICubicShiftFrequency]
    positivity
  · dsimp [huaTypeIICubicShiftFrequency]
    calc
      36 * l ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁ * η₂ ≤
          36 * l ^ 3 * D * D * D * P₀ * P₀ := by gcongr
      _ = 36 * l ^ 3 * D ^ 3 * P₀ ^ 2 := by ring

/-- Hua's exact nonzero-frequency multiplicity bound for cubic degree:
each of the five positive shifts divides `z`, giving at most `d(z)^5`
tuples. The fixed factor `36*l³` is retained in the frequency. -/
theorem card_hua_typeII_cubic_shift_frequency_fiber_le
    (l D P₀ z : ℕ) (hz : 0 < z) :
    ((huaTypeIICubicShiftBox D P₀).filter
      (fun x => huaTypeIICubicShiftFrequency l x = z)).card ≤
        z.divisors.card ^ 5 := by
  classical
  let S := (huaTypeIICubicShiftBox D P₀).filter
    (fun x => huaTypeIICubicShiftFrequency l x = z)
  let B := z.divisors.product (z.divisors.product
    (z.divisors.product (z.divisors.product z.divisors)))
  have hsubset : S ⊆ B := by
    rintro ⟨ξ₁, ξ₂, ξ₃, η₁, η₂⟩ hx
    have hfreq : 36 * l ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁ * η₂ = z := by
      exact (Finset.mem_filter.mp hx).2
    have hdvd₁ : ξ₁ ∣ z := by
      refine ⟨36 * l ^ 3 * ξ₂ * ξ₃ * η₁ * η₂, ?_⟩
      rw [← hfreq]
      ring
    have hdvd₂ : ξ₂ ∣ z := by
      refine ⟨36 * l ^ 3 * ξ₁ * ξ₃ * η₁ * η₂, ?_⟩
      rw [← hfreq]
      ring
    have hdvd₃ : ξ₃ ∣ z := by
      refine ⟨36 * l ^ 3 * ξ₁ * ξ₂ * η₁ * η₂, ?_⟩
      rw [← hfreq]
      ring
    have hdvd₄ : η₁ ∣ z := by
      refine ⟨36 * l ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₂, ?_⟩
      rw [← hfreq]
      ring
    have hdvd₅ : η₂ ∣ z := by
      refine ⟨36 * l ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁, ?_⟩
      rw [← hfreq]
      ring
    change (ξ₁, ξ₂, ξ₃, η₁, η₂) ∈ B
    simpa [B] using (show
      ξ₁ ∈ z.divisors ∧ ξ₂ ∈ z.divisors ∧ ξ₃ ∈ z.divisors ∧
        η₁ ∈ z.divisors ∧ η₂ ∈ z.divisors from
      ⟨Nat.mem_divisors.mpr ⟨hdvd₁, hz.ne'⟩,
        Nat.mem_divisors.mpr ⟨hdvd₂, hz.ne'⟩,
        Nat.mem_divisors.mpr ⟨hdvd₃, hz.ne'⟩,
        Nat.mem_divisors.mpr ⟨hdvd₄, hz.ne'⟩,
        Nat.mem_divisors.mpr ⟨hdvd₅, hz.ne'⟩⟩)
  calc
    _ = S.card := rfl
    _ ≤ B.card := Finset.card_le_card hsubset
    _ = z.divisors.card ^ 5 := by simp [B, pow_succ, mul_assoc]

/-- A source-shaped divisor-rich exceptional-tuple bound. Grouping the
five positive shifts by their exact nonzero frequency costs `d(z)^5`;
the threshold supplies one more divisor factor, so Hua's sixth unweighted
divisor moment controls the total exceptional count. This is still only
arithmetic multiplicity, not a bound for the regular phase sums. -/
theorem hua_typeII_cubic_divisor_rich_shift_count_le
    (l D P₀ M : ℕ) (hl : 0 < l)
    (hM : 36 * l ^ 3 * D ^ 3 * P₀ ^ 2 ≤ M)
    (T : ℝ) :
    T * (((huaTypeIICubicShiftBox D P₀).filter
      (fun x => T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))).card : ℝ) ≤
        (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 63 := by
  classical
  let E := (huaTypeIICubicShiftBox D P₀).filter
    (fun x => T ≤ ((huaTypeIICubicShiftFrequency l x).divisors.card : ℝ))
  let I := Finset.Icc 1 M
  have hmaps : ∀ x ∈ E, huaTypeIICubicShiftFrequency l x ∈ I := by
    intro x hx
    have hbox : x ∈ huaTypeIICubicShiftBox D P₀ :=
      (Finset.mem_filter.mp hx).1
    obtain ⟨hpos, hupper⟩ :=
      hua_typeII_cubic_shift_frequency_bounds l D P₀ hl hbox
    exact Finset.mem_Icc.mpr ⟨hpos, hupper.trans hM⟩
  have hgroup : (E.card : ℝ) =
      ∑ z ∈ I, (((E.filter
        (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ)) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hpoint : ∀ z ∈ I,
      T * (((E.filter
        (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ)) ≤
          (z.divisors.card : ℝ) ^ 6 := by
    intro z hzI
    have hz : 0 < z := (Finset.mem_Icc.mp hzI).1
    by_cases hrich : T ≤ (z.divisors.card : ℝ)
    · have hsubset :
          E.filter (fun x => huaTypeIICubicShiftFrequency l x = z) ⊆
            (huaTypeIICubicShiftBox D P₀).filter
              (fun x => huaTypeIICubicShiftFrequency l x = z) := by
        intro x hx
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩
      have hcard : ((E.filter
          (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) ≤
          (z.divisors.card : ℝ) ^ 5 := by
        have hnat := (Finset.card_le_card hsubset).trans
          (card_hua_typeII_cubic_shift_frequency_fiber_le l D P₀ z hz)
        exact_mod_cast hnat
      calc
        T * ((E.filter
            (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ) ≤
            (z.divisors.card : ℝ) * (z.divisors.card : ℝ) ^ 5 := by
          exact (mul_le_mul_of_nonneg_right hrich (by positivity)).trans
            (mul_le_mul_of_nonneg_left hcard (by positivity))
        _ = (z.divisors.card : ℝ) ^ 6 := by ring
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
  have hmoment : (∑ z ∈ I, (z.divisors.card : ℝ) ^ 6) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 63 := by
    simpa [I, divisorUnweightedMoment] using
      (divisorUnweightedMoment_le_envelope M 6)
  calc
    T * (E.card : ℝ) =
        ∑ z ∈ I, T * (((E.filter
          (fun x => huaTypeIICubicShiftFrequency l x = z)).card : ℝ)) := by
      rw [hgroup, Finset.mul_sum]
    _ ≤ ∑ z ∈ I, (z.divisors.card : ℝ) ^ 6 :=
      Finset.sum_le_sum hpoint
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 63 := hmoment

#print axioms hua_typeII_cubic_shift_frequency_bounds
#print axioms card_hua_typeII_cubic_shift_frequency_fiber_le
#print axioms hua_typeII_cubic_divisor_rich_shift_count_le

end SystolicGrowth.CookMagyarCircle
