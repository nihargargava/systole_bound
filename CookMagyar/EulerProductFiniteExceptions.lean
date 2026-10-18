module

public import CookMagyar.EulerProduct

@[expose] public section

/-!
# Euler products with finitely many exceptional factors

This is the exact interface needed when the large-prime estimate is proved
only beyond a cutoff.  The finite exceptional factors are required to be
positive, while summability is checked on the complement subtype.
-/

namespace SystolicGrowth
namespace CookMagyarEulerProduct

open scoped BigOperators

theorem summable_compl_of_prime_rpow_bound
    (S : Finset Nat.Primes) {mu : Nat.Primes → ℝ} {C delta : ℝ}
    (_hC : 0 ≤ C) (hdelta : 0 < delta)
    (hbound : ∀ p : Nat.Primes, p ∉ S →
      |mu p - 1| ≤ C * (p : ℝ) ^ (-(1 + delta))) :
    Summable (fun p : {p : Nat.Primes // p ∉ S} ↦ |mu p - 1|) := by
  have hseries : Summable (fun p : {p : Nat.Primes // p ∉ S} ↦
      C * (p : ℝ) ^ (-(1 + delta))) := by
    apply Summable.mul_left
    exact (Nat.Primes.summable_rpow.mpr (by linarith)).subtype
      (fun p : Nat.Primes ↦ p ∉ S)
  apply hseries.of_nonneg_of_le
  · intro p
    exact abs_nonneg _
  · intro p
    exact hbound p.1 p.2

theorem zero_lt_tprod_of_pos_of_summable_abs_sub_one_compl
    {ι : Type*} (S : Finset ι) {f : ι → ℝ}
    (hpos : ∀ i, 0 < f i)
    (hcomp : Summable (fun i : {i : ι // i ∉ S} ↦ |f i - 1|)) :
    0 < ∏' i, f i := by
  have habs : Summable (fun i : ι ↦ |f i - 1|) := by
    apply Summable.add_compl (s := S) Summable.of_finite
    exact hcomp
  exact zero_lt_tprod_of_pos_of_summable_abs_sub_one hpos habs

theorem zero_lt_tprod_of_pos_of_compl_prime_rpow_bound
    (S : Finset Nat.Primes) {f : Nat.Primes → ℝ} {C delta : ℝ}
    (_hC : 0 ≤ C) (hdelta : 0 < delta)
    (hpos : ∀ p, 0 < f p)
    (hbound : ∀ p : Nat.Primes, p ∉ S →
      |f p - 1| ≤ C * (p : ℝ) ^ (-(1 + delta))) :
    0 < ∏' p, f p := by
  apply zero_lt_tprod_of_pos_of_summable_abs_sub_one_compl S hpos
  exact summable_compl_of_prime_rpow_bound S _hC hdelta hbound

/-- A quantitative Euler-product lower bound with finitely many exceptional
factors. The exceptional factors only need target-independent positive lower
bounds; on the complement, deviations are bounded by a summable half-unit
majorant. -/
theorem tprod_lower_of_finite_exceptions
    {ι : Type*} (S : Finset ι) {f b a : ι → ℝ}
    (ha : Summable (fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => a i))
    (ha_half : ∀ i : ι, i ∉ S → a i ≤ 1 / 2)
    (hdev : ∀ i : ι, i ∉ S → |f i - 1| ≤ a i)
    (hfin : ∀ i : ι, i ∈ S → 0 < b i ∧ b i ≤ f i) :
    (∏ i ∈ S, b i) *
        Real.exp (-2 * ∑' i : {i : ι // i ∈ (S : Set ι)ᶜ}, a i) ≤
      ∏' i, f i := by
  classical
  have htail : Summable (fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => f i - 1) := by
    apply Summable.of_norm_bounded ha
    intro i
    simpa only [Real.norm_eq_abs] using hdev i i.property
  have hcomp : Multipliable (fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => f i) := by
    have h := Real.multipliable_one_add_of_summable htail
    have heq :
        (fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => (1 : ℝ) + (f i - 1)) =
          (fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => f i) := by
      funext i
      ring
    simpa only [heq] using h
  have hprod : (∏ i ∈ S, b i) ≤ ∏ i ∈ S, f i := by
    apply Finset.prod_le_prod₀ (s := S) (f := b) (g := f)
    · intro i hi
      exact (hfin i hi).1.le
    · intro i hi
      exact (hfin i hi).2
  have htailLower :
      Real.exp (-2 * ∑' i : {i : ι // i ∈ (S : Set ι)ᶜ}, a i) ≤
        ∏' i : {i : ι // i ∈ (S : Set ι)ᶜ}, f i :=
    exp_neg_two_tsum_le_tprod
      (f := fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => f i)
      (a := fun i : {i : ι // i ∈ (S : Set ι)ᶜ} => a i) ha
      (fun i => ha_half i i.property) (fun i => hdev i i.property)
  have htailPos :
      0 < Real.exp (-2 * ∑' i : {i : ι // i ∈ (S : Set ι)ᶜ}, a i) :=
    Real.exp_pos _
  have hfinPos : 0 < ∏ i ∈ S, f i := by
    apply Finset.prod_pos (s := S) (f := f)
    intro i hi
    exact (hfin i hi).1.trans_le (hfin i hi).2
  have hstep :
      (∏ i ∈ S, b i) *
          Real.exp (-2 * ∑' i : {i : ι // i ∈ (S : Set ι)ᶜ}, a i) ≤
        (∏ i ∈ S, f i) *
          (∏' i : {i : ι // i ∈ (S : Set ι)ᶜ}, f i) :=
    (mul_le_mul_of_nonneg_right hprod htailPos.le).trans
      (mul_le_mul_of_nonneg_left htailLower hfinPos.le)
  have hfinite : Multipliable (fun i : (S : Set ι) => f i) :=
    Multipliable.of_finite
  have hsplit :
      (∏ i ∈ S, f i) *
          (∏' i : {i : ι // i ∈ (S : Set ι)ᶜ}, f i) =
        ∏' i, f i := by
    have h := Multipliable.tprod_mul_tprod_compl
      (s := (S : Set ι)) hfinite hcomp
    simpa only [Finset.tprod_subtype'] using h
  exact hstep.trans_eq hsplit

end CookMagyarEulerProduct
end SystolicGrowth
