module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.FiniteFourier
public import CookMagyar.LocalNonsingular
public import CookMagyar.LocalSmallPrimes

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Local solutions and normalized congruence counts

This file connects the explicit unit solutions from `LocalNonsingular` to
the exact finite Fourier count.  It also defines the finite-level
normalization whose prime-power limit is the local factor in the singular
series.
-/

variable {q : ℕ} [NeZero q]

/-- Positivity of the finite count is exactly existence of a unit tuple. -/
theorem unitCubicSolutionCount_pos_iff {n : ℕ} {T : ZMod q} :
    0 < unitCubicSolutionCount n T ↔
      ∃ x : Fin n → (ZMod q)ˣ, unitCubicSum x = T := by
  classical
  unfold unitCubicSolutionCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- A nonsingular unit solution gives a positive finite local count. -/
theorem unitCubicSolutionCount_pos_of_nonsingular
    {n : ℕ} {T : ZMod q}
    (s : CookMagyarLocal.NonsingularUnitSolution q n T) :
    0 < unitCubicSolutionCount n T := by
  rw [unitCubicSolutionCount_pos_iff]
  let x : Fin n → (ZMod q)ˣ := fun i ↦ (s.isUnit_point i).unit
  refine ⟨x, ?_⟩
  calc
    unitCubicSum x =
        ∑ i, CookMagyarLocal.cubicResidue (s.point i) := by
      unfold unitCubicSum
      apply Finset.sum_congr rfl
      intro i _hi
      rw [(s.isUnit_point i).unit_spec]
      rfl
    _ = T := s.equation

/-- The same bridge for the unit-solution structure used by the explicit
two- and three-adic constructions. -/
theorem unitCubicSolutionCount_pos_of_unitSolution
    {n : ℕ} {T : ZMod q}
    (s : CookMagyarLocal.UnitCubicSolution q n T) :
    0 < unitCubicSolutionCount n T := by
  rw [unitCubicSolutionCount_pos_iff]
  let x : Fin n → (ZMod q)ˣ := fun i ↦ (s.isUnit_point i).unit
  refine ⟨x, ?_⟩
  calc
    unitCubicSum x =
        ∑ i, CookMagyarLocal.cubicResidue (s.point i) := by
      unfold unitCubicSum
      apply Finset.sum_congr rfl
      intro i _hi
      rw [(s.isUnit_point i).unit_spec]
      rfl
    _ = T := s.equation

/-- For every prime `q ≥ 5`, every target has a positive unit count once
there are at least five variables. -/
theorem unitCubicSolutionCount_pos_of_prime_ge_five
    {n : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hn5 : 5 ≤ n)
    (T : ZMod q) : 0 < unitCubicSolutionCount n T := by
  rcases CookMagyarLocal.nonsingularUnitSolution_exists hq hq5 hn5 T with ⟨s⟩
  exact unitCubicSolutionCount_pos_of_nonsingular s

/-- Positivity at every two-power modulus for Cook--Magyar targets. -/
theorem unitCubicSolutionCount_pos_two_power
    {n k T : ℕ} (hn : 2 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    0 < unitCubicSolutionCount n (T : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rcases CookMagyarLocal.twoAdic_unit_solution_of_dvd_twentyFour hn k T hT with ⟨s⟩
  exact unitCubicSolutionCount_pos_of_unitSolution s

/-- Positivity at every three-power modulus for Cook--Magyar targets. -/
theorem unitCubicSolutionCount_pos_three_power
    {n k T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    0 < unitCubicSolutionCount n (T : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rcases CookMagyarLocal.threeAdic_unit_solution_of_dvd_twentyFour hn k T hT with
    ⟨s, _hderivative⟩
  exact unitCubicSolutionCount_pos_of_unitSolution s

/-- The finite-level local-density normalization
`q * M(q,T) / φ(q)^n`.  For `q=p^k`, its limit as `k→∞` is the local
factor used by Cook--Magyar. -/
noncomputable def normalizedUnitCubicCount
    (n : ℕ) (T : ZMod q) : ℝ :=
  (q : ℝ) * unitCubicSolutionCount n T /
    (Nat.totient q : ℝ) ^ n

theorem normalizedUnitCubicCount_nonneg (n : ℕ) (T : ZMod q) :
    0 ≤ normalizedUnitCubicCount n T := by
  unfold normalizedUnitCubicCount
  positivity

theorem normalizedUnitCubicCount_pos
    {n : ℕ} {T : ZMod q} (hq : 1 < q)
    (hcount : 0 < unitCubicSolutionCount n T) :
    0 < normalizedUnitCubicCount n T := by
  unfold normalizedUnitCubicCount
  have hq0 : 0 < (q : ℝ) := by positivity
  have hcount_real : 0 < (unitCubicSolutionCount n T : ℝ) := by
    exact_mod_cast hcount
  have hphi : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  positivity

/-- The normalized count at the prime-power modulus `p^k`. -/
noncomputable def primePowerLocalDensityApproximation
    (p k n T : ℕ) (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact normalizedUnitCubicCount n (T : ZMod (p ^ k))

/-- A real number is the local density if the normalized prime-power counts
converge to it. -/
def HasPrimeLocalDensity (p n T : ℕ) (hp : p.Prime) (mu : ℝ) : Prop :=
  Filter.Tendsto
    (fun k ↦ primePowerLocalDensityApproximation p k n T hp)
    Filter.atTop (nhds mu)

theorem hasPrimeLocalDensity_unique
    {p n T : ℕ} {hp : p.Prime} {mu nu : ℝ}
    (hmu : HasPrimeLocalDensity p n T hp mu)
    (hnu : HasPrimeLocalDensity p n T hp nu) : mu = nu :=
  tendsto_nhds_unique hmu hnu

end CookMagyarFiniteFourier
end SystolicGrowth
