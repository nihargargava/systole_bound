module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepNineBlocks

@[expose] public section

/-!
# Fixed Type-II inner support at source modulus one

At `Q=1`, the source congruence is automatic. The factor-count and parity
conditions therefore define a single set of inner indices before the outer
index `u` is chosen. This file proves that the remaining `u`-dependence is
exactly the variable interval used by Hua's Type-II mean-square lemma.
The quotient condition `u*v ≤ P/m` is converted by an equivalence, not by
weakening its upper endpoint.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- The Hua step-nine inner support independent of the outer index `u`.
The positivity predicate is explicit even though divisor membership already
implies it. -/
noncomputable def huaStepNineFixedSupport (H Y s parity : ℕ) : Finset ℕ := by
  classical
  exact H.divisors.filter fun v =>
    0 < v ∧ (primeFactorsAtLeastCutoff Y v).card + 1 = s ∧
      (v.primeFactors.card + 1) % 2 = parity

/-- Dividing the real lower endpoint by a positive `u` is equivalent to the
original strict lower condition on the product `u*v`. -/
theorem hua_stepNine_lower_product_iff_interval
    (P u v : ℕ) (lambda₂ : ℝ) (hu : 0 < u) :
    (P : ℝ) / Real.rpow (Real.log P) lambda₂ < (u * v : ℕ) ↔
      ((P : ℝ) / Real.rpow (Real.log P) lambda₂) / u < (v : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  constructor
  · intro h
    apply (div_lt_iff₀ huR).2
    simpa only [Nat.cast_mul, mul_comm] using h
  · intro h
    have h' := (div_lt_iff₀ huR).1 h
    simpa only [Nat.cast_mul, mul_comm] using h'

/-- For positive `m,u`, the natural quotient bound is *equivalent* to the
real variable upper endpoint. The first step uses the exact integer
`Nat.le_div_iff_mul_le`, not a floor relaxation. -/
theorem hua_stepNine_quotient_product_iff_interval
    (P m u v : ℕ) (hm : 0 < m) (hu : 0 < u) :
    u * v ≤ P / m ↔
      (v : ℝ) ≤ ((P : ℝ) / m) / u := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hreal : ((u * v * m : ℕ) : ℝ) ≤ P ↔
      (v : ℝ) ≤ ((P : ℝ) / m) / u := by
    rw [le_div_iff₀ huR, le_div_iff₀ hmR]
    simp only [Nat.cast_mul]
    constructor <;> intro h <;> nlinarith
  constructor
  · intro h
    apply hreal.mp
    exact_mod_cast (Nat.le_div_iff_mul_le hm).mp h
  · intro h
    apply (Nat.le_div_iff_mul_le hm).2
    have h' := hreal.mpr h
    exact_mod_cast h'

/-- At `Q=1`, every step-nine source fiber is *exactly* the fixed inner
support intersected with Hua's variable interval. The target residue `t`
is arbitrary because all residues agree modulo one. -/
theorem huaStepNineSourceVFiber_modOne_eq_fixedSupport_filter
    (P m t s parity u : ℕ) (lambda₂ lambda₃ : ℝ)
    (hm : 0 < m) (hu : 0 < u) :
    huaStepNineVFiber (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
      (huaStepEightSourceCondition P m 1 t lambda₂) =
    (huaStepNineFixedSupport (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity).filter
      (fun v : ℕ => 0 < v ∧
        ((P : ℝ) / Real.rpow (Real.log P) lambda₂) / u < (v : ℝ) ∧
        (v : ℝ) ≤ ((P : ℝ) / m) / u) := by
  classical
  ext v
  simp only [huaStepNineVFiber, huaStepNineFixedSupport, Finset.mem_filter]
  simp only [huaStepEightSourceCondition]
  constructor
  · rintro ⟨hdiv, hupper, hcount, hparity, hlower, _hmod⟩
    have hv : 0 < v := Nat.pos_of_mem_divisors hdiv
    exact ⟨⟨hdiv, hv, hcount, hparity⟩, hv,
      (hua_stepNine_lower_product_iff_interval P u v lambda₂ hu).mp hlower,
      (hua_stepNine_quotient_product_iff_interval P m u v hm hu).mp hupper⟩
  · rintro ⟨⟨hdiv, _hv, hcount, hparity⟩, _, hlower, hupper⟩
    exact ⟨hdiv,
      (hua_stepNine_quotient_product_iff_interval P m u v hm hu).mpr hupper,
      hcount, hparity,
      (hua_stepNine_lower_product_iff_interval P u v lambda₂ hu).mpr hlower,
      Nat.modEq_one⟩

#print axioms hua_stepNine_lower_product_iff_interval
#print axioms hua_stepNine_quotient_product_iff_interval
#print axioms huaStepNineSourceVFiber_modOne_eq_fixedSupport_filter

end SystolicGrowth.CookMagyarCircle
