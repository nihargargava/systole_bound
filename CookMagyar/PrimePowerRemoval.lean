module

public import CookMagyar.CircleMethod

@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Separating odd primes from prime powers

The Cook--Magyar asymptotic counts tuples with von-Mangoldt weights.  This
file performs the exact finite partition of that count into tuples consisting
entirely of odd primes and the complementary (prime-power/prime-two) part.
The asymptotic estimate showing that the latter part is smaller is analytic;
the bookkeeping and the extraction of an actual tuple are proved here.
-/

/-- An odd-prime natural number. -/
def IsOddPrime (p : ℕ) : Prop := p.Prime ∧ p ≠ 2

/-- Every coordinate of a bounded tuple is an odd prime. -/
def IsOddPrimeTuple {n N : ℕ} (x : Fin n → Fin (N + 1)) : Prop :=
  ∀ i, IsOddPrime (x i)

/-- The von-Mangoldt weight supported on exact odd-prime solutions. -/
noncomputable def cubicOddPrimeRepresentation
    (n N T : ℕ) : ℝ := by
  classical
  exact ∑ x : Fin n → Fin (N + 1),
    if (∑ i, primeCubic (x i)) = T ∧ IsOddPrimeTuple x then
      tupleVonMangoldtWeight x
    else 0

/-- The complementary weight: solutions having at least one coordinate
which is not an odd prime. -/
noncomputable def cubicDiscardedRepresentation
    (n N T : ℕ) : ℝ := by
  classical
  exact ∑ x : Fin n → Fin (N + 1),
    if (∑ i, primeCubic (x i)) = T ∧ ¬IsOddPrimeTuple x then
      tupleVonMangoldtWeight x
    else 0

theorem cubicOddPrimeRepresentation_nonneg (n N T : ℕ) :
    0 ≤ cubicOddPrimeRepresentation n N T := by
  classical
  unfold cubicOddPrimeRepresentation tupleVonMangoldtWeight
  exact Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact Finset.prod_nonneg fun i _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

theorem cubicDiscardedRepresentation_nonneg (n N T : ℕ) :
    0 ≤ cubicDiscardedRepresentation n N T := by
  classical
  unfold cubicDiscardedRepresentation tupleVonMangoldtWeight
  exact Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact Finset.prod_nonneg fun i _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- Exact partition of the von-Mangoldt count. -/
theorem cubicVonMangoldtRepresentation_eq_oddPrime_add_discarded
    (n N T : ℕ) :
    cubicVonMangoldtRepresentation n N T =
      cubicOddPrimeRepresentation n N T +
        cubicDiscardedRepresentation n N T := by
  classical
  unfold cubicVonMangoldtRepresentation cubicOddPrimeRepresentation
    cubicDiscardedRepresentation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases heq : (∑ i, primeCubic (x i)) = T
  · by_cases hp : IsOddPrimeTuple x <;> simp [heq, hp]
  · simp [heq]

/-- A bounded representation by odd primes. -/
def IsOddPrimeCubicRepresentation (n N T : ℕ) : Prop :=
  ∃ x : Fin n → Fin (N + 1),
    (∑ i, primeCubic (x i)) = T ∧ IsOddPrimeTuple x

private theorem tupleVonMangoldtWeight_pos_of_oddPrimes {n N : ℕ}
    {x : Fin n → Fin (N + 1)} (hx : IsOddPrimeTuple x) :
    0 < tupleVonMangoldtWeight x := by
  classical
  unfold tupleVonMangoldtWeight
  exact Finset.prod_pos fun i _ ↦ by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hx i).1]
    exact Real.log_pos (by exact_mod_cast (hx i).1.one_lt)

/-- Positivity of the prime-only part extracts an actual odd-prime tuple. -/
theorem cubicOddPrimeRepresentation_pos_iff (n N T : ℕ) :
    0 < cubicOddPrimeRepresentation n N T ↔
      IsOddPrimeCubicRepresentation n N T := by
  classical
  unfold cubicOddPrimeRepresentation IsOddPrimeCubicRepresentation
  have hnonneg : ∀ x : Fin n → Fin (N + 1),
      0 ≤ if (∑ i, primeCubic (x i)) = T ∧ IsOddPrimeTuple x then
        tupleVonMangoldtWeight x else 0 := by
    intro x
    split_ifs
    · exact Finset.prod_nonneg fun i _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  rw [Finset.sum_pos_iff_of_nonneg (fun x _hx ↦ hnonneg x)]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    by_cases hgood : (∑ i, primeCubic (x i)) = T ∧ IsOddPrimeTuple x
    · exact ⟨x, hgood⟩
    · simp [hgood] at hx
  · rintro ⟨x, heq, hp⟩
    refine ⟨x, ?_⟩
    have hw := tupleVonMangoldtWeight_pos_of_oddPrimes hp
    simpa [heq, hp] using hw

/-- The abstract final step of prime-power removal: a main count strictly
larger than its discarded part contains an odd-prime solution. -/
theorem exists_oddPrimeCubicRepresentation_of_discarded_lt_total
    {n N T : ℕ}
    (h : cubicDiscardedRepresentation n N T <
      cubicVonMangoldtRepresentation n N T) :
    IsOddPrimeCubicRepresentation n N T := by
  rw [cubicVonMangoldtRepresentation_eq_oddPrime_add_discarded] at h
  have hpos : 0 < cubicOddPrimeRepresentation n N T := by linarith
  exact (cubicOddPrimeRepresentation_pos_iff n N T).mp hpos

/-- A quantitative form convenient for the circle-method estimates. -/
theorem exists_oddPrimeCubicRepresentation_of_lower_upper
    {n N T : ℕ} {main error : ℝ}
    (htotal : main ≤ cubicVonMangoldtRepresentation n N T)
    (hdiscard : cubicDiscardedRepresentation n N T ≤ error)
    (hdom : error < main) :
    IsOddPrimeCubicRepresentation n N T :=
  exists_oddPrimeCubicRepresentation_of_discarded_lt_total
    (hdiscard.trans_lt (hdom.trans_le htotal))

end CookMagyarCircle
end SystolicGrowth
