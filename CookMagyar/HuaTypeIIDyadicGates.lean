module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepNineBlocks
public import CookMagyar.HuaDivisorBound

@[expose] public section

open Filter

/-!
# Dyadic source gates for Hua's Type-II blocks

The source estimates use the dyadic lower endpoint `D = 2^k`. A selected
prime `u` in the corresponding block satisfies `D < u ≤ 2D`; the cutoff
and square-root endpoints therefore transfer to the two size gates on `D`.
These are arithmetic preparations, not the Type-II cancellation estimate.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- A nonempty actual source block inherits Hua's lower and upper size gates
once the two scalar cutoff comparisons are known. -/
theorem huaStepNineDyadicBlock_source_gates
    (P k u sigma5 sigma6 : ℕ) (lambda₃ : ℝ)
    (hu : u ∈ huaStepNineDyadicBlock
      (primeFactorsAtLeastCutoff
        (Nat.ceil (Real.rpow (Real.log P) lambda₃))
        (huaStepEightSieveProduct P)) k)
    (hcut : 2 * (Real.log (P : ℝ)) ^ sigma5 <
      Real.rpow (Real.log P) lambda₃)
    (hroot : (Nat.sqrt P : ℝ) <
      (P : ℝ) / (Real.log P) ^ sigma6) :
    (Real.log (P : ℝ)) ^ sigma5 < (2 ^ k : ℕ) ∧
      ((2 ^ k : ℕ) : ℝ) < (P : ℝ) / (Real.log P) ^ sigma6 ∧
      2 ^ k < u ∧ u ≤ 2 * 2 ^ k := by
  have hprimeMem : u ∈ primeFactorsAtLeastCutoff
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (huaStepEightSieveProduct P) := (Finset.mem_filter.mp hu).1
  obtain ⟨hprime, hcutU, hrootU⟩ :=
    huaStepNineOuterPrime_source_bounds P u lambda₃ hprimeMem
  obtain ⟨hDltU, hUle2D⟩ :=
    mem_huaStepNineDyadicBlock_imp hu hprime.two_le
  have hUle2D' : u ≤ 2 * 2 ^ k := by
    simpa [pow_succ, mul_comm] using hUle2D
  have hUle2Dreal : (u : ℝ) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast hUle2D'
  have hDltRoot : ((2 ^ k : ℕ) : ℝ) < Nat.sqrt P := by
    exact_mod_cast (lt_of_lt_of_le hDltU hrootU)
  refine ⟨?_, hDltRoot.trans hroot, hDltU, hUle2D'⟩
  have h : 2 * (Real.log (P : ℝ)) ^ sigma5 <
      2 * ((2 ^ k : ℕ) : ℝ) := lt_of_lt_of_le (hcut.trans_le hcutU) hUle2Dreal
  linarith

/-- Choosing the outer-prime cutoff exponent above the lower-block exponent
eventually makes every nonempty dyadic block large enough for Lemma 6.3. -/
theorem eventually_huaTypeII_lowerDyadicGate
    (sigma5 : ℕ) (lambda₃ : ℝ)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃) :
    ∀ᶠ P : ℕ in atTop,
      2 * (Real.log (P : ℝ)) ^ sigma5 <
        Real.rpow (Real.log P) lambda₃ := by
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (2 : ℝ)] with P hL
  let L : ℝ := Real.log P
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hpowpos : 0 < L ^ sigma5 := pow_pos hLpos _
  have hlt : 2 * L ^ sigma5 < L ^ (sigma5 + 1) := by
    rw [pow_succ]
    have h := mul_lt_mul_of_pos_left (show (2 : ℝ) < L by
      dsimp [L]; exact hL) hpowpos
    nlinarith
  have hle : L ^ (sigma5 + 1) ≤ Real.rpow L lambda₃ := by
    calc
      L ^ (sigma5 + 1) = Real.rpow L ((sigma5 + 1 : ℕ) : ℝ) := by
        exact (Real.rpow_natCast L (sigma5 + 1)).symm
      _ ≤ Real.rpow L lambda₃ :=
        Real.rpow_le_rpow_of_exponent_le hLone hLambda
  exact hlt.trans_le hle

/-- A square-root upper endpoint is eventually strictly below the
`P/(log P)^sigma6` Type-II upper gate. -/
theorem eventually_huaTypeII_upperDyadicGate (sigma6 : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      (Nat.sqrt P : ℝ) < (P : ℝ) / (Real.log P) ^ sigma6 := by
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_natSqrt_le_scale_div_log_pow (sigma6 + 1),
    hlog.eventually_gt_atTop (2 : ℝ)] with P hroot hL
  have hP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hLpos : 0 < Real.log (P : ℝ) := by linarith
  have hpowpos : 0 < (Real.log (P : ℝ)) ^ sigma6 := pow_pos hLpos _
  have hpowlt : (Real.log (P : ℝ)) ^ sigma6 <
      (Real.log (P : ℝ)) ^ (sigma6 + 1) := by
    rw [pow_succ]
    have h := mul_lt_mul_of_pos_left (show (1 : ℝ) < Real.log P by linarith)
      hpowpos
    nlinarith
  have hquot : (P : ℝ) / (Real.log P) ^ (sigma6 + 1) <
      (P : ℝ) / (Real.log P) ^ sigma6 := by
    apply (div_lt_div_iff₀ (pow_pos hLpos _) hpowpos).2
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hpowlt hP
  exact hroot.2.trans_lt hquot

/-- Every nonempty source dyadic block eventually meets both numerical
`D`-gates in Hua's Type-II mean-square statement, uniformly in the block
index and its selected prime. -/
theorem eventually_huaStepNineDyadicBlock_source_gates
    (sigma5 sigma6 : ℕ) (lambda₃ : ℝ)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃) :
    ∀ᶠ P : ℕ in atTop, ∀ k u : ℕ,
      u ∈ huaStepNineDyadicBlock
        (primeFactorsAtLeastCutoff
          (Nat.ceil (Real.rpow (Real.log P) lambda₃))
          (huaStepEightSieveProduct P)) k →
        (Real.log (P : ℝ)) ^ sigma5 < (2 ^ k : ℕ) ∧
        ((2 ^ k : ℕ) : ℝ) < (P : ℝ) / (Real.log P) ^ sigma6 ∧
        2 ^ k < u ∧ u ≤ 2 * 2 ^ k := by
  filter_upwards [eventually_huaTypeII_lowerDyadicGate sigma5 lambda₃ hLambda,
    eventually_huaTypeII_upperDyadicGate sigma6] with P hcut hroot
  intro k u hu
  exact huaStepNineDyadicBlock_source_gates
    P k u sigma5 sigma6 lambda₃ hu hcut hroot

#print axioms huaStepNineDyadicBlock_source_gates
#print axioms eventually_huaTypeII_lowerDyadicGate
#print axioms eventually_huaTypeII_upperDyadicGate
#print axioms eventually_huaStepNineDyadicBlock_source_gates

end SystolicGrowth.CookMagyarCircle
