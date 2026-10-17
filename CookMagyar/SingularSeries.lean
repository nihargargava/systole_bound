module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.FiniteMultiplicativity
public import CookMagyar.LocalCount
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Singular-series objects for the diagonal cubic

This file gives concrete definitions of the complete-sum coefficient
`B(T,q)`, its finite truncations, the full singular series, and the formal
prime local factors.  Convergence and the uniform Euler-tail bound are
subsequent theorems; no default value or abstract placeholder is hidden in
these definitions.
-/

/-- The complete-sum coefficient `B(T,q)` for a positive modulus.  The
outer frequency is restricted to units, exactly as in the classical
singular-series expansion. -/
noncomputable def singularSeriesCoefficient
    (q n T : ℕ) (hq : q ≠ 0) : ℂ := by
  letI : NeZero q := ⟨hq⟩
  exact ((Nat.totient q : ℂ)⁻¹) ^ n *
    ∑ a : (ZMod q)ˣ,
      unitCubicExponentialSum (a : ZMod q) ^ n *
        standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q)))

/-- The coefficient extended by zero at the non-modulus `q=0`. -/
noncomputable def singularSeriesTerm (n T q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else singularSeriesCoefficient q n T hq

@[simp] theorem singularSeriesTerm_zero (n T : ℕ) :
    singularSeriesTerm n T 0 = 0 := by
  simp [singularSeriesTerm]

theorem singularSeriesTerm_of_pos (n T : ℕ) {q : ℕ} (hq : 0 < q) :
    singularSeriesTerm n T q = singularSeriesCoefficient q n T hq.ne' := by
  simp [singularSeriesTerm, hq.ne']

/-- A singular-series coefficient depends on the target only through its
residue modulo the positive denominator. -/
theorem singularSeriesTerm_eq_of_target_eq_mod
    (n q T U : ℕ) (hq : 0 < q)
    (hTU : (T : ZMod q) = (U : ZMod q)) :
    singularSeriesTerm n T q = singularSeriesTerm n U q := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [singularSeriesTerm_of_pos n T hq, singularSeriesTerm_of_pos n U hq]
  unfold singularSeriesCoefficient
  rw [hTU]

/-- The modulus-one singular-series coefficient is exactly one. -/
theorem singularSeriesTerm_modOne_eq_one (n T : ℕ) :
    singularSeriesTerm n T 1 = 1 := by
  haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
  have hz (z : ZMod 1) : z = 0 := Subsingleton.elim _ _
  rw [singularSeriesTerm_of_pos n T (by norm_num)]
  simp [singularSeriesCoefficient, unitCubicExponentialSum,
    standardAdditiveCharacter, hz]

/-- The maximum norm of the denominator-`q` singular-series coefficient over
all target residues. The zero-modulus value is set to zero; only positive
denominators are used in the circle method. -/
noncomputable def singularSeriesTermNormMaximum (n q : ℕ) : ℝ := by
  classical
  by_cases hq : q = 0
  · exact 0
  · letI : NeZero q := ⟨hq⟩
    exact Finset.univ.sup' ⟨0, Finset.mem_univ _⟩
      (fun t : ZMod q => ‖singularSeriesTerm n t.val q‖)

/-- Every integer-target coefficient is bounded by the finite residue
maximum at its denominator. -/
theorem norm_singularSeriesTerm_le_maximum
    (n q T : ℕ) (hq : 0 < q) :
    ‖singularSeriesTerm n T q‖ ≤ singularSeriesTermNormMaximum n q := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have htarget : singularSeriesTerm n T q =
      singularSeriesTerm n ((T : ZMod q).val) q :=
    singularSeriesTerm_eq_of_target_eq_mod n q T _ hq
      (ZMod.natCast_zmod_val (T : ZMod q)).symm
  rw [htarget]
  simp only [singularSeriesTermNormMaximum, dif_neg hq.ne']
  exact Finset.le_sup'
    (fun t : ZMod q => ‖singularSeriesTerm n t.val q‖)
    (Finset.mem_univ (T : ZMod q))

/-- The finite residue maximum is attained at an actual residue class. -/
theorem singularSeriesTermNormMaximum_attained
    (n q : ℕ) (hq : 0 < q) :
    ∃ t : ZMod q,
      singularSeriesTermNormMaximum n q =
        ‖singularSeriesTerm n t.val q‖ := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨t, ht, hmax⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (ZMod q)).Nonempty)
      (fun t : ZMod q => ‖singularSeriesTerm n t.val q‖)
  refine ⟨t, ?_⟩
  simpa [singularSeriesTermNormMaximum, hq.ne'] using hmax

/-- The denominator-one coefficient maximum has the expected unit value. -/
theorem singularSeriesTermNormMaximum_one (n : ℕ) :
    singularSeriesTermNormMaximum n 1 = 1 := by
  obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n 1 (by norm_num)
  rw [singularSeriesTerm_modOne_eq_one] at ht
  simpa using ht

/-- The denominator-truncated singular series. -/
noncomputable def truncatedSingularSeries (n T Q : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm n T q

@[simp] theorem truncatedSingularSeries_zero (n T : ℕ) :
    truncatedSingularSeries n T 0 = 0 := by
  simp [truncatedSingularSeries]

/-- The full singular series, defined as a countable sum of its exact
complete-sum coefficients. -/
noncomputable def singularSeries (n T : ℕ) : ℂ :=
  ∑' q : ℕ, singularSeriesTerm n T q

/-- The formal local factor at a prime `p`, written as
`1 + ∑_{k≥1} B(T,p^k)`. -/
noncomputable def primeLocalFactor (p n T : ℕ) : ℂ :=
  1 + ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 1))

/-- The normalized finite congruence count, regarded as a complex number.
This is the finite-level expression which the local factor limit equals. -/
noncomputable def complexNormalizedUnitCubicCount
    (q n T : ℕ) (hq : q ≠ 0) : ℂ := by
  letI : NeZero q := ⟨hq⟩
  exact (q : ℂ) * (unitCubicSolutionCount n (T : ZMod q) : ℂ) /
    (Nat.totient q : ℂ) ^ n

theorem complexNormalizedUnitCubicCount_of_real
    (q n T : ℕ) (hq : q ≠ 0) :
    complexNormalizedUnitCubicCount q n T hq = by
      letI : NeZero q := ⟨hq⟩
      exact (normalizedUnitCubicCount n (T : ZMod q) : ℂ) := by
  letI : NeZero q := ⟨hq⟩
  unfold complexNormalizedUnitCubicCount normalizedUnitCubicCount
  push_cast
  rfl

end CookMagyarFiniteFourier
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm_eq_of_target_eq_mod
#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm_modOne_eq_one
#print axioms SystolicGrowth.CookMagyarFiniteFourier.norm_singularSeriesTerm_le_maximum
#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTermNormMaximum_attained
#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTermNormMaximum_one
