module

public import CookMagyar.EulerProduct
public import CookMagyar.LocalFactorBridge
public import CookMagyar.PrimePowerStationaryPhase

@[expose] public section

/-!
# Euler-product bridge for real local factors

The abstract Euler-product positivity theorem is applied here to the actual
real parts of the cubic local factors.  The hypotheses are deliberately the
precise remaining arithmetic obligations: positivity and a summable prime
power-saving deviation.
-/

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

open CookMagyarEulerProduct

theorem zero_lt_realPrimeLocalFactor_tprod_of_rpow_bound
    {n T : ℕ} {C delta : ℝ}
    (hpos : ∀ p : Nat.Primes, 0 <
      (primeLocalFactor (p : ℕ) n T).re)
    (hdelta : 0 < delta)
    (hbound : ∀ p : Nat.Primes,
      |(primeLocalFactor (p : ℕ) n T).re - 1| ≤
        C * (p : ℝ) ^ (-(1 + delta))) :
    0 < ∏' p : Nat.Primes, (primeLocalFactor (p : ℕ) n T).re := by
  exact zero_lt_tprod_of_prime_rpow_bound hpos hdelta hbound

theorem primeLocalFactor_three_real_pos_of_admissible_target
    {n T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    0 < (primeLocalFactor 3 n T).re :=
  CookMagyarPrimePower.primeLocalFactor_three_re_pos hn hT

/-- Both exceptional primes below five have positive local factors on
Cook--Magyar's admissible targets. -/
theorem primeLocalFactor_real_pos_of_prime_le_three
    {p n T : ℕ} (hp : p.Prime) (hp3 : p ≤ 3)
    (hn : 1 ≤ n) (hT : 24 ∣ T) :
    0 < (primeLocalFactor p n T).re := by
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact CookMagyarPrimePower.primeLocalFactor_two_re_pos_of_dvd_twentyFour
      (by omega) hT
  · exact primeLocalFactor_three_real_pos_of_admissible_target hn hT

end CookMagyarFiniteFourier
end SystolicGrowth
