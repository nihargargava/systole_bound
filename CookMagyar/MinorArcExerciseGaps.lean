module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimeMinorArcVaughan
public import CookMagyar.HuaStepNineBlocks
public import CookMagyar.HuaStepNineFixedSupport
public import CookMagyar.HuaStepEightLargeFactorRecount
public import CookMagyar.HuaPrimeSieveIdentity
public import CookMagyar.HuaPrimeSmallDivisors
public import CookMagyar.HuaTypeIISquareExpansion
public import CookMagyar.HuaTypeIISupportCount
public import CookMagyar.HuaTypeIIDiagonal
public import CookMagyar.HuaTypeIIPairReorder
public import CookMagyar.HuaTypeIIPhaseDifference
public import CookMagyar.HuaTypeIIFrequency
public import CookMagyar.HuaTypeIIDifferencing
public import CookMagyar.HuaTypeIICauchy
public import CookMagyar.HuaTypeIIMixedDifference
public import CookMagyar.HuaTypeIIMixedSupport
public import CookMagyar.HuaTypeIIInnerWindows
public import CookMagyar.HuaTypeIIJointMoment
public import CookMagyar.HuaTypeIIExceptionalFrequency
public import CookMagyar.HuaTypeIIFrequencyEnvelope
public import CookMagyar.HuaTypeIIFrequencyNormalized
public import CookMagyar.HuaTypeIIFrequencyLogSaving
public import CookMagyar.HuaTypeIIPairSymmetry
public import CookMagyar.HuaTypeIIDyadicGates
public import CookMagyar.OrdinaryWeylMinorArc
public import CookMagyar.MinorArcHighMoment
public import CookMagyar.PrimePowerMass
public import CookMagyar.CubicAbelPhase
public import CookMagyar.MainTerm

@[expose] public section

/-!
# Proved minor-arc source estimates and consumers

The unchanged MIN-01 Type-II mean square and MIN-03 rational prime estimate
are proved from the actual Hua source ranges. MIN-02, prefix transfer, Abel
summation and proper-prime-power control yield MIN-08; the 32nd-moment
consumer gives the logarithmic minor-arc integral error.

Constants and thresholds are uniform in the lower cubic coefficients.
The final cutoff is independent of the arity, error fraction and target.
Preserve all declaration contracts and source cutoffs when modifying proofs.
-/

open Filter MeasureTheory Asymptotics ComplexConjugate
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs CookMagyarVaughan CookMagyarMajorArc

/-- The actual finite support in Hua's `Q=1` Type-II inner sum. Keeping it
named makes the two endpoint inequalities visible in every later sum. -/
noncomputable def exerciseHuaTypeIIInnerSupport (P l : ℕ) (P' : ℝ)
    (V : Finset ℕ) (u : ℕ) : Finset ℕ := by
  classical
  exact V.filter (fun v : ℕ =>
    0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
      (v : ℝ) ≤ ((P : ℝ) / l) / u)

/-- The actual Hua step-nine source fiber at modulus one is the precise
fixed-support interval used by MIN-01. In particular its upper endpoint
still expresses the original natural quotient `P / m` exactly. -/
theorem exercise_hua_typeII_support_eq_stepNine_modOne
    (P m t s parity u : ℕ) (lambda₂ lambda₃ : ℝ)
    (hm : 0 < m) (hu : 0 < u) :
    exerciseHuaTypeIIInnerSupport P m
      ((P : ℝ) / Real.rpow (Real.log P) lambda₂)
      (huaStepNineFixedSupport (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity) u =
    huaStepNineVFiber (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
      (huaStepEightSourceCondition P m 1 t lambda₂) := by
  simpa only [exerciseHuaTypeIIInnerSupport] using
    (huaStepNineSourceVFiber_modOne_eq_fixedSupport_filter
      P m t s parity u lambda₂ lambda₃ hm hu).symm

/-- **MIN-01b, proved finite count.** The named Hua inner support has at most
`P/(lD)` entries on a dyadic outer block with `D<u`. -/
theorem exercise_card_hua_typeII_inner_support_le
    (P l D u : ℕ) (P' : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) (hDu : D < u) :
    ((exerciseHuaTypeIIInnerSupport P l P' V u).card : ℝ) ≤
      ((P : ℝ) / l) / D := by
  simpa only [exerciseHuaTypeIIInnerSupport] using
    card_hua_typeII_interval_support_le P l D u P' V hl hD hDu

/-- The exact variable-endpoint inner sum in the `Q=1` cubic specialization
of Hua Lemma 6.3. The set `V` is fixed before the outer variable is chosen. -/
noncomputable def exerciseHuaTypeIIInner (P l : ℕ) (P' : ℝ)
    (V : Finset ℕ) (a q : ℕ) (b c d : ℝ) (u : ℕ) : ℂ := by
  classical
  exact ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
    generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)

/-- Clipping the arbitrary fixed inner set to the source's positive
`P₀` interval leaves the actual support unchanged on this dyadic block. -/
theorem exercise_hua_typeII_inner_support_eq_clipped
    (P l D u : ℕ) (P' : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) (hDu : D < u) :
    exerciseHuaTypeIIInnerSupport P l P' V u =
      exerciseHuaTypeIIInnerSupport P l P'
        (V ∩ Finset.Icc 1 (Nat.floor (((P : ℝ) / l) / D))) u := by
  classical
  have hsub := hua_typeII_interval_support_subset_positive_Icc
    P l D u P' V hl hD hDu
  ext v
  simp only [exerciseHuaTypeIIInnerSupport, Finset.mem_filter, Finset.mem_inter]
  constructor
  · intro hv
    exact ⟨⟨hv.1, hsub (Finset.mem_filter.mpr hv)⟩, hv.2⟩
  · rintro ⟨⟨hvV, _⟩, hvpred⟩
    exact ⟨hvV, hvpred⟩

/-- The source mean square itself, not merely its cardinality, is unchanged
by clipping `V` to the uniform positive inner interval. The next Holder
stage may therefore use its proved interval envelope without assuming that
the original arbitrary `V` was already an interval. -/
theorem exercise_hua_typeII_mean_square_eq_clipped
    (P l D D' a q : ℕ) (P' b c d : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) =
      ∑ u ∈ Finset.Icc (D + 1) D',
        ‖exerciseHuaTypeIIInner P l P'
          (V ∩ Finset.Icc 1 (Nat.floor (((P : ℝ) / l) / D)))
          a q b c d u‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro u hu
  have hDu : D < u := by have := (Finset.mem_Icc.mp hu).1; omega
  unfold exerciseHuaTypeIIInner
  rw [exercise_hua_typeII_inner_support_eq_clipped P l D u P' V hl hD hDu]

#print axioms exercise_hua_typeII_inner_support_eq_clipped
#print axioms exercise_hua_typeII_mean_square_eq_clipped

/-- **MIN-01l, proved source inner sum.** At modulus one, the exercise's
variable-interval sum is exactly the step-nine source fiber sum, including
its original product argument in the cubic phase. -/
theorem exercise_hua_typeII_inner_eq_stepNine_modOne
    (P m t s parity u a q : ℕ) (lambda₂ lambda₃ b c d : ℝ)
    (hm : 0 < m) (hu : 0 < u) :
    exerciseHuaTypeIIInner P m
      ((P : ℝ) / Real.rpow (Real.log P) lambda₂)
      (huaStepNineFixedSupport (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity)
      a q b c d u =
    ∑ v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
      (huaStepEightSourceCondition P m 1 t lambda₂),
      generalCubicPhase ((a : ℝ) / q) b c d (m * (u * v)) := by
  unfold exerciseHuaTypeIIInner
  rw [exercise_hua_typeII_support_eq_stepNine_modOne
    P m t s parity u lambda₂ lambda₃ hm hu]
  simp only [Nat.mul_assoc]

/-- **MIN-03a, proved source-to-exercise dyadic sum.** At source modulus
one, every step-nine dyadic fiber is the exact inner sum to which MIN-01
and MIN-02 apply; no analytic estimate is used in this identity. -/
theorem exercise_sum_huaStepEightSourcePairs_eq_sum_stepNineDyadicInner_modOne
    (P m t s parity a q : ℕ) (lambda₂ lambda₃ b c d : ℝ)
    (hm : 0 < m) :
    (∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m 1 t lambda₂),
        generalCubicPhase ((a : ℝ) / q) b c d (m * (pair.1 * pair.2))) =
      ∑ k ∈ Finset.Icc 0 (Nat.log 2 (Nat.sqrt P)),
        ∑ u ∈ huaStepNineDyadicBlock
            (primeFactorsAtLeastCutoff
              (Nat.ceil (Real.rpow (Real.log P) lambda₃))
              (huaStepEightSieveProduct P)) k,
          exerciseHuaTypeIIInner P m
            ((P : ℝ) / Real.rpow (Real.log P) lambda₂)
            (huaStepNineFixedSupport (huaStepEightSieveProduct P)
              (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity)
            a q b c d u := by
  classical
  rw [sum_huaStepEightSourcePairs_eq_sum_stepNineDyadicFibers
    P m 1 t s parity lambda₂ lambda₃
    (generalCubicPhase ((a : ℝ) / q) b c d)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  have huSource : u ∈ primeFactorsAtLeastCutoff
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (huaStepEightSieveProduct P) :=
    (Finset.mem_filter.mp hu).1
  have huPos : 0 < u :=
    ((mem_huaStepNineOuterPrime_iff P
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) u).mp huSource).1.pos
  exact (exercise_hua_typeII_inner_eq_stepNine_modOne
    P m t s parity u a q lambda₂ lambda₃ b c d hm huPos).symm

/-- **MIN-03b, proved dyadic range.** The selected-prime block is a
permitted outer set for MIN-02 with `D = 2^k` and `D' = 2^(k+1)`. -/
theorem exercise_huaStepNineDyadicBlock_subset_typeII_interval
    (P k : ℕ) (lambda₃ : ℝ) :
    huaStepNineDyadicBlock
        (primeFactorsAtLeastCutoff
          (Nat.ceil (Real.rpow (Real.log P) lambda₃))
          (huaStepEightSieveProduct P)) k ⊆
      Finset.Icc (2 ^ k + 1) (2 ^ (k + 1)) := by
  intro u hu
  have huSource : u ∈ primeFactorsAtLeastCutoff
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (huaStepEightSieveProduct P) :=
    (Finset.mem_filter.mp hu).1
  have huTwo : 2 ≤ u :=
    ((mem_huaStepNineOuterPrime_iff P
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) u).mp huSource).1.two_le
  obtain ⟨huLo, huHi⟩ := mem_huaStepNineDyadicBlock_imp hu huTwo
  exact Finset.mem_Icc.mpr ⟨by omega, huHi⟩

/-- **MIN-01a, proved finite algebra.** This is the exact diagonal/off-diagonal
identity for Hua's variable-endpoint inner sum. The remaining Type-II work
starts with bounding these two displayed sums, not re-expanding a norm. -/
theorem exercise_hua_typeII_mean_square_split
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) =
      (∑ u ∈ Finset.Icc (D + 1) D',
        ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
          ‖generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)‖ ^ 2) +
      (∑ u ∈ Finset.Icc (D + 1) D',
        ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
          ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).erase v,
            (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
              conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re) := by
  classical
  simpa only [exerciseHuaTypeIIInner] using
    sum_norm_sum_sq_eq_diagonal_add_offDiagonal
      (Finset.Icc (D + 1) D')
      (exerciseHuaTypeIIInnerSupport P l P' V)
      (fun u v => generalCubicPhase ((a : ℝ) / q) b c d (l * u * v))

/-- **MIN-01c, proved diagonal.** After the exact split, all remaining
Type-II cancellation lies in the off-diagonal sum. -/
theorem exercise_hua_typeII_diagonal_le
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ)
    (hl : 0 < l) (hD : 0 < D) (hD' : D' ≤ 2 * D) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
        ‖generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)‖ ^ 2) ≤
      (P : ℝ) / l := by
  simpa only [exerciseHuaTypeIIInnerSupport] using
    hua_typeII_diagonal_le P l D D' a q P' V b c d hl hD hD'

/-- **MIN-01d, proved finite reindexing.** Each ordered off-diagonal pair
is summed over precisely those outer indices satisfying *both* variable
endpoint conditions. Its summand is an ordinary cubic phase in `u` with
the exact leading frequency needed by Hua's divisor argument. -/
theorem exercise_hua_typeII_offDiagonal_reindex
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
        ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).erase v,
          (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
            conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re) =
      ∑ v ∈ V, ∑ w ∈ V.erase v,
        ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
          v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
          w ∈ exerciseHuaTypeIIInnerSupport P l P' V u),
          (generalCubicPhase
            (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
            (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
            (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u).re := by
  classical
  have hW : ∀ u ∈ Finset.Icc (D + 1) D',
      exerciseHuaTypeIIInnerSupport P l P' V u ⊆ V := by
    intro u hu
    unfold exerciseHuaTypeIIInnerSupport
    exact Finset.filter_subset _ _
  calc
    _ = ∑ v ∈ V, ∑ w ∈ V.erase v,
          ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
            v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
            w ∈ exerciseHuaTypeIIInnerSupport P l P' V u),
            (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
              conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re :=
      sum_offDiagonal_reindex (Finset.Icc (D + 1) D') V
        (exerciseHuaTypeIIInnerSupport P l P' V) hW _
    _ = _ := by simp_rw [hua_typeII_phase_mul_conj]

/-- **MIN-01e, proved endpoint bookkeeping.** Membership in the reordered
outer support means that *both* inner indices satisfy their actual strict
lower and weak upper interval endpoints. The fixed-set membership remains
visible and independent of the outer index. -/
theorem exercise_hua_typeII_pair_window_iff
    (P l D D' : ℕ) (P' : ℝ) (V : Finset ℕ) (v w u : ℕ) :
    u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
      v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
      w ∈ exerciseHuaTypeIIInnerSupport P l P' V u) ↔
      D + 1 ≤ u ∧ u ≤ D' ∧
      v ∈ V ∧ 0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
        (v : ℝ) ≤ ((P : ℝ) / l) / u ∧
      w ∈ V ∧ 0 < w ∧ P' / (u : ℝ) < (w : ℝ) ∧
        (w : ℝ) ≤ ((P : ℝ) / l) / u := by
  classical
  simp only [Finset.mem_filter, Finset.mem_Icc,
    exerciseHuaTypeIIInnerSupport]
  tauto

/-- **MIN-01f, proved endpoint swap.** Positive outer and inner indices
allow the source's variable-`v` inequalities to be read as a fixed interval
in the outer variable `u`, with strictness preserved. -/
theorem exercise_hua_typeII_interval_swap
    (P₁ P' : ℝ) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    (P' / (u : ℝ) < (v : ℝ) ∧ (v : ℝ) ≤ P₁ / u) ↔
      (P' / (v : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ P₁ / v) := by
  have hu' : 0 < (u : ℝ) := by exact_mod_cast hu
  have hv' : 0 < (v : ℝ) := by exact_mod_cast hv
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hv').2
      simpa only [mul_comm] using (div_lt_iff₀ hu').1 hlo
    · apply (le_div_iff₀ hv').2
      simpa only [mul_comm] using (le_div_iff₀ hu').1 hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hu').2
      simpa only [mul_comm] using (div_lt_iff₀ hv').1 hlo
    · apply (le_div_iff₀ hu').2
      simpa only [mul_comm] using (le_div_iff₀ hv').1 hhi

/-- **MIN-01g, proved pair orientation.** The real off-diagonal contribution
counts each unordered pair twice. We keep only `w<v`, making the natural
frequency `v³-w³` strictly positive for the divisor step. -/
theorem exercise_hua_typeII_offDiagonal_eq_two_lowerOrdered
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
        ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).erase v,
          (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
            conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re) =
      2 * ∑ u ∈ Finset.Icc (D + 1) D',
        ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
          ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).filter
              (fun w => w < v),
            (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
              conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re := by
  classical
  calc
    _ = ∑ u ∈ Finset.Icc (D + 1) D',
          2 * (∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
            ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).filter
                (fun w => w < v),
              (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
                conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply sum_offDiagonal_eq_two_sum_lt
      intro v w
      exact mul_conj_re_symm _ _
    _ = _ := by rw [Finset.mul_sum]

/-- **MIN-01h, proved positive-frequency reindexing.** The `w<v` half of
the off-diagonal sum is indexed by one fixed ordered pair from `V`, then by
the exact outer window on which both inner indices occur. -/
theorem exercise_hua_typeII_lowerOrdered_reindex
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
        ∑ w ∈ (exerciseHuaTypeIIInnerSupport P l P' V u).filter
            (fun w => w < v),
          (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
            conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re) =
      ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v),
        ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
          v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
          w ∈ exerciseHuaTypeIIInnerSupport P l P' V u),
          (generalCubicPhase
            (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
            (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
            (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u).re := by
  classical
  have hW : ∀ u ∈ Finset.Icc (D + 1) D',
      exerciseHuaTypeIIInnerSupport P l P' V u ⊆ V := by
    intro u hu
    unfold exerciseHuaTypeIIInnerSupport
    exact Finset.filter_subset _ _
  calc
    _ = ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v),
          ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
            v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
            w ∈ exerciseHuaTypeIIInnerSupport P l P' V u),
            (generalCubicPhase ((a : ℝ) / q) b c d (l * u * v) *
              conj (generalCubicPhase ((a : ℝ) / q) b c d (l * u * w))).re :=
      sum_lt_reindex (Finset.Icc (D + 1) D') V
        (exerciseHuaTypeIIInnerSupport P l P' V) hW _
    _ = _ := by simp_rw [hua_typeII_phase_mul_conj]

/-- **MIN-01i, proved source-ready identity.** The exact Type-II mean
square is its bounded diagonal plus twice the ordered off-diagonal cubic
sum. No analytic cancellation is used in this equality. -/
theorem exercise_hua_typeII_mean_square_eq_diagonal_add_ordered
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) =
      (∑ u ∈ Finset.Icc (D + 1) D',
        ∑ v ∈ exerciseHuaTypeIIInnerSupport P l P' V u,
          ‖generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)‖ ^ 2) +
      2 * ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v),
        ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
          v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
          w ∈ exerciseHuaTypeIIInnerSupport P l P' V u),
          (generalCubicPhase
            (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
            (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
            (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u).re := by
  rw [exercise_hua_typeII_mean_square_split,
    exercise_hua_typeII_offDiagonal_eq_two_lowerOrdered,
    exercise_hua_typeII_lowerOrdered_reindex]

/-- **MIN-01j, proved common outer interval.** For a fixed positive pair
in `V`, the variable inner-support tests are exactly the intersection of
three intervals in the outer index, with both strict lower bounds retained. -/
theorem exercise_hua_typeII_ordered_pair_window_iff
    (P l D D' : ℕ) (P' : ℝ) (V : Finset ℕ) (v w u : ℕ)
    (hvV : v ∈ V) (hwV : w ∈ V) (hv : 0 < v) (hw : 0 < w) :
    u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
      v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
      w ∈ exerciseHuaTypeIIInnerSupport P l P' V u) ↔
      D < u ∧ u ≤ D' ∧
        P' / (v : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / v ∧
        P' / (w : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / w := by
  constructor
  · intro h
    obtain ⟨huLo, huHi, _, _, hvLo, hvHi, _, _, hwLo, hwHi⟩ :=
      (exercise_hua_typeII_pair_window_iff P l D D' P' V v w u).1 h
    have hu : 0 < u := by omega
    obtain ⟨hvLo', hvHi'⟩ :=
      (exercise_hua_typeII_interval_swap ((P : ℝ) / l) P' u v hu hv).1
        ⟨hvLo, hvHi⟩
    obtain ⟨hwLo', hwHi'⟩ :=
      (exercise_hua_typeII_interval_swap ((P : ℝ) / l) P' u w hu hw).1
        ⟨hwLo, hwHi⟩
    exact ⟨by omega, huHi, hvLo', hvHi', hwLo', hwHi'⟩
  · rintro ⟨hDu, huHi, hvLo, hvHi, hwLo, hwHi⟩
    have hu : 0 < u := by omega
    obtain ⟨hvLo', hvHi'⟩ :=
      (exercise_hua_typeII_interval_swap ((P : ℝ) / l) P' u v hu hv).2
        ⟨hvLo, hvHi⟩
    obtain ⟨hwLo', hwHi'⟩ :=
      (exercise_hua_typeII_interval_swap ((P : ℝ) / l) P' u w hu hw).2
        ⟨hwLo, hwHi⟩
    exact (exercise_hua_typeII_pair_window_iff P l D D' P' V v w u).2
      ⟨by omega, huHi, hvV, hv, hvLo', hvHi', hwV, hw, hwLo', hwHi'⟩

/-- The support of one ordered pair in the actual Type-II square expansion
is exactly the common outer interval used by the finite-differencing lemma.
No endpoint or positivity test is discarded. -/
theorem exercise_hua_typeII_ordered_pair_support_eq_commonWindow
    (P l D D' : ℕ) (P' : ℝ) (V : Finset ℕ) (v w : ℕ)
    (hvV : v ∈ V) (hwV : w ∈ V) (hv : 0 < v) (hw : 0 < w) :
    (Finset.Icc (D + 1) D').filter (fun u =>
      v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
      w ∈ exerciseHuaTypeIIInnerSupport P l P' V u) =
      huaTypeIICommonOuterWindow P l D D' v w P' := by
  classical
  ext u
  exact (exercise_hua_typeII_ordered_pair_window_iff
    P l D D' P' V v w u hvV hwV hv hw).trans
    (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').symm

/-- First finite differencing of the precise cubic ordered-pair sum in
`exercise_hua_typeII_mean_square_eq_diagonal_add_ordered`. Both members
of each positive-shift pair remain in the original variable support. -/
theorem exercise_hua_typeII_ordered_pair_firstDifference
    (P l D D' v w a q : ℕ) (P' b c : ℝ) (V : Finset ℕ)
    (hvV : v ∈ V) (hwV : w ∈ V) (hv : 0 < v) (hw : 0 < w) :
    let U := (Finset.Icc (D + 1) D').filter (fun u =>
      v ∈ exerciseHuaTypeIIInnerSupport P l P' V u ∧
      w ∈ exerciseHuaTypeIIInnerSupport P l P' V u)
    let A : ℝ := ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B : ℝ := b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C : ℝ := c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    ‖∑ u ∈ U, generalCubicPhase A B C 0 u‖ ^ 2 =
      (U.card : ℝ) +
        2 * (∑ h ∈ Finset.Icc 1 D',
          ∑ u ∈ (Finset.range (D' + 1 - h)).filter
            (fun u => u ∈ U ∧ u + h ∈ U),
              generalCubicPhase 0
                (3 * A * h)
                (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
                (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u).re := by
  dsimp only
  rw [exercise_hua_typeII_ordered_pair_support_eq_commonWindow
    P l D D' P' V v w hvV hwV hv hw]
  exact hua_typeII_ordered_pair_commonWindow_firstDifference
    P l D D' v w a q P' b c

#print axioms exercise_hua_typeII_ordered_pair_support_eq_commonWindow
#print axioms exercise_hua_typeII_ordered_pair_firstDifference

/-- The actual mean square is bounded by its proved diagonal and norms of
the common-window sums, with the lower inner index outside. Clipping is
justified for the original arbitrary fixed `V`, not assumed. -/
theorem exercise_hua_typeII_mean_square_le_clipped_ordered_norms
    (P l D D' a q : ℕ) (P' b c d : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) (hD' : D' ≤ 2 * D) :
    let P₀ := Nat.floor (((P : ℝ) / l) / D)
    let W := V ∩ Finset.Icc 1 P₀
    (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) ≤
      (P : ℝ) / l + 2 *
        (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v),
          ‖∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
            generalCubicPhase
              (((a : ℝ) / q) * (l : ℝ) ^ 3 *
                ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
              (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
              (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u‖) := by
  classical
  dsimp only
  let W := V ∩ Finset.Icc 1 (Nat.floor (((P : ℝ) / l) / D))
  let f := fun v w u : ℕ => generalCubicPhase
    (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
    (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
    (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
  have hpos {v : ℕ} (hv : v ∈ W) : 0 < v := by
    have := (Finset.mem_Icc.mp (Finset.mem_inter.mp hv).2).1
    omega
  have hordered :
      (∑ v ∈ W, ∑ w ∈ W.filter (fun w => w < v),
        ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
          v ∈ exerciseHuaTypeIIInnerSupport P l P' W u ∧
          w ∈ exerciseHuaTypeIIInnerSupport P l P' W u), (f v w u).re) =
      ∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v),
        (∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P', f v w u).re := by
    calc
      _ = ∑ v ∈ W, ∑ w ∈ W.filter (fun w => w < v),
          (∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P', f v w u).re := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro w hw
        have hwW := (Finset.mem_filter.mp hw).1
        rw [exercise_hua_typeII_ordered_pair_support_eq_commonWindow
          P l D D' P' W v w hv hwW (hpos hv) (hpos hwW), Complex.re_sum]
      _ = _ := by
        apply Finset.sum_comm'
        intro v w
        simp only [Finset.mem_filter]
        tauto
  have hnorm :
      (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v),
        (∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P', f v w u).re) ≤
      ∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v),
        ‖∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P', f v w u‖ := by
    apply Finset.sum_le_sum
    intro w hw
    apply Finset.sum_le_sum
    intro v hv
    exact Complex.re_le_norm _
  rw [exercise_hua_typeII_mean_square_eq_clipped P l D D' a q P' b c d V hl hD]
  rw [exercise_hua_typeII_mean_square_eq_diagonal_add_ordered]
  change _ + 2 * (∑ v ∈ W, ∑ w ∈ W.filter (fun w => w < v),
    ∑ u ∈ (Finset.Icc (D + 1) D').filter (fun u =>
      v ∈ exerciseHuaTypeIIInnerSupport P l P' W u ∧
      w ∈ exerciseHuaTypeIIInnerSupport P l P' W u), (f v w u).re) ≤ _
  rw [hordered]
  have hdiag := exercise_hua_typeII_diagonal_le P l D D' a q P' W b c d hl hD hD'
  linarith

#print axioms exercise_hua_typeII_mean_square_le_clipped_ordered_norms

/-- Two finite eighth-power Holder steps reduce the entire clipped
off-diagonal norm sum to the full positive-interval eighth moments. Only
nonnegative quantities are enlarged to those intervals. -/
theorem exercise_hua_typeII_clipped_ordered_norms_eighth_le
    (P l D D' a q : ℕ) (P' b c : ℝ) (V : Finset ℕ) :
    let P₀ := Nat.floor (((P : ℝ) / l) / D)
    let W := V ∩ Finset.Icc 1 P₀
    let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
      generalCubicPhase
        (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
        (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
        (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
    (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 8 ≤
      (P₀ : ℝ) ^ 14 *
        (∑ w ∈ Finset.Icc 1 P₀, ∑ v ∈ Finset.Icc 1 P₀, ‖S v w‖ ^ 8) := by
  classical
  dsimp only
  let P₀ := Nat.floor (((P : ℝ) / l) / D)
  let W := V ∩ Finset.Icc 1 P₀
  let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
    generalCubicPhase
      (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
      (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
  let row := fun w => ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖
  let moment := fun w => ∑ v ∈ Finset.Icc 1 P₀, ‖S v w‖ ^ 8
  have hW : W ⊆ Finset.Icc 1 P₀ := Finset.inter_subset_right
  have hcard : (W.card : ℝ) ≤ P₀ := by
    have h := Finset.card_le_card hW
    simpa [Nat.card_Icc] using (Nat.cast_le (α := ℝ)).mpr h
  have hrow (w : ℕ) : row w ^ 8 ≤ (P₀ : ℝ) ^ 7 * moment w := by
    exact hua_typeII_fixedLowerPair_holder_eighth_interval
      P l D D' w a q P₀ P' b c W hW
  have hsum : (∑ w ∈ W, moment w) ≤ ∑ w ∈ Finset.Icc 1 P₀, moment w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hW
    intro w hw hnot
    dsimp [moment]
    positivity
  calc
    (∑ w ∈ W, row w) ^ 8 ≤ (W.card : ℝ) ^ 7 * (∑ w ∈ W, row w ^ 8) :=
      pow_sum_le_card_mul_sum_pow (by intro w hw; dsimp [row]; positivity) 7
    _ ≤ (P₀ : ℝ) ^ 7 * (∑ w ∈ W, row w ^ 8) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hcard 7
    _ ≤ (P₀ : ℝ) ^ 7 * (∑ w ∈ W, (P₀ : ℝ) ^ 7 * moment w) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (by intro w hw; exact hrow w)
    _ = (P₀ : ℝ) ^ 14 * (∑ w ∈ W, moment w) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (P₀ : ℝ) ^ 14 * (∑ w ∈ Finset.Icc 1 P₀, moment w) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

#print axioms exercise_hua_typeII_clipped_ordered_norms_eighth_le

/-- The complete finite thirty-second-power bound for the original clipped
ordered norm sum. The only remaining cancellation quantity is the actual
positive five-shift frequency envelope; all diagonal losses are explicit. -/
theorem exercise_hua_typeII_clipped_ordered_norms_thirtyTwo_le
    (P l D D' a q : ℕ) (P' b c : ℝ) (V : Finset ℕ)
    (hD : 1 ≤ D) (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let P₀ := Nat.floor (((P : ℝ) / l) / D)
    let W := V ∩ Finset.Icc 1 P₀
    let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
      generalCubicPhase
        (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
        (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
        (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
    (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 32 ≤
      (P₀ : ℝ) ^ 60 *
        (8 * (648 ^ 4 * (P₀ : ℝ) ^ 4 * (D : ℝ) ^ 28 +
          1024 ^ 4 * (D : ℝ) ^ 25 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
            (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
              16 * (P₀ : ℝ) *
                (∑ x ∈ huaTypeIICubicShiftBox D P₀,
                  linearDistanceEnvelope (P₀ : ℝ)
                    (((a : ℝ) / q) *
                      (huaTypeIICubicShiftFrequency l x : ℝ)))))) := by
  classical
  dsimp only
  let P₀ := Nat.floor (((P : ℝ) / l) / D)
  let W := V ∩ Finset.Icc 1 P₀
  let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
    generalCubicPhase
      (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
      (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
  let moment := fun w => ∑ v ∈ Finset.Icc 1 P₀, ‖S v w‖ ^ 8
  let B := 8 * (648 ^ 4 * (P₀ : ℝ) ^ 4 * (D : ℝ) ^ 28 +
    1024 ^ 4 * (D : ℝ) ^ 25 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
      (6 * (D : ℝ) ^ 3 * (P₀ : ℝ) ^ 3 +
        16 * (P₀ : ℝ) *
          (∑ x ∈ huaTypeIICubicShiftBox D P₀,
            linearDistanceEnvelope (P₀ : ℝ)
              (((a : ℝ) / q) * (huaTypeIICubicShiftFrequency l x : ℝ)))))
  have hmoment (w : ℕ) : moment w ^ 4 ≤ B := by
    exact hua_typeII_interval_eighth_four_le_frequencyEnvelope
      P l D D' w a q P₀ P' b c hD hDD' hD'
  have hsum : (∑ w ∈ Finset.Icc 1 P₀, moment w ^ 4) ≤ (P₀ : ℝ) * B := by
    calc
      _ ≤ ∑ w ∈ Finset.Icc 1 P₀, B := Finset.sum_le_sum (by
        intro w hw
        exact hmoment w)
      _ = _ := by simp [Nat.card_Icc]
  have hholder : (∑ w ∈ Finset.Icc 1 P₀, moment w) ^ 4 ≤
      (P₀ : ℝ) ^ 3 * (∑ w ∈ Finset.Icc 1 P₀, moment w ^ 4) := by
    simpa [Nat.card_Icc] using pow_sum_le_card_mul_sum_pow
      (s := Finset.Icc 1 P₀) (f := moment)
      (by intro w hw; dsimp [moment]; positivity) 3
  have heighth := exercise_hua_typeII_clipped_ordered_norms_eighth_le
    P l D D' a q P' b c V
  calc
    (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 32 =
        ((∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 8) ^ 4 := by ring
    _ ≤ ((P₀ : ℝ) ^ 14 * (∑ w ∈ Finset.Icc 1 P₀, moment w)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) heighth 4
    _ = (P₀ : ℝ) ^ 56 * (∑ w ∈ Finset.Icc 1 P₀, moment w) ^ 4 := by ring
    _ ≤ (P₀ : ℝ) ^ 56 *
        ((P₀ : ℝ) ^ 3 * (∑ w ∈ Finset.Icc 1 P₀, moment w ^ 4)) :=
      mul_le_mul_of_nonneg_left hholder (by positivity)
    _ ≤ (P₀ : ℝ) ^ 56 * ((P₀ : ℝ) ^ 3 * ((P₀ : ℝ) * B)) := by
      gcongr
    _ = (P₀ : ℝ) ^ 60 * B := by ring

#print axioms exercise_hua_typeII_clipped_ordered_norms_thirtyTwo_le

/-- The actual clipped ordered norm sum, normalized into its three scalar
losses. Positivity of the floor endpoint is supplied by the source dyadic
gate via `hua_typeII_floor_inner_endpoint_bounds`, not assumed in MIN-01. -/
theorem exercise_hua_typeII_clipped_ordered_norms_normalized_le
    (P l D D' a q : ℕ) (P' b c : ℝ) (V : Finset ℕ)
    (hD : 1 ≤ D) (hDD' : D ≤ D') (hD' : D' ≤ 2 * D)
    (hN : 0 < Nat.floor (((P : ℝ) / l) / D)) :
    let N := Nat.floor (((P : ℝ) / l) / D)
    let W := V ∩ Finset.Icc 1 N
    let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
      generalCubicPhase
        (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
        (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
        (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
    let E := ∑ x ∈ huaTypeIICubicShiftBox D N,
      linearDistanceEnvelope (N : ℝ)
        (((a : ℝ) / q) * (huaTypeIICubicShiftFrequency l x : ℝ))
    (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 32 ≤
      (2 : ℝ) ^ 64 * (D : ℝ) ^ 32 * (N : ℝ) ^ 64 *
        (1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
          E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) := by
  classical
  dsimp only
  let N := Nat.floor (((P : ℝ) / l) / D)
  let W := V ∩ Finset.Icc 1 N
  let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
    generalCubicPhase
      (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
      (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
  let E := ∑ x ∈ huaTypeIICubicShiftBox D N,
    linearDistanceEnvelope (N : ℝ)
      (((a : ℝ) / q) * (huaTypeIICubicShiftFrequency l x : ℝ))
  have hE : 0 ≤ E := Finset.sum_nonneg (by
    intro x hx
    exact linearDistanceEnvelope_nonneg (Nat.cast_nonneg N))
  have hpoly := hua_typeII_moment_polynomial_le_normalized D D' N E hD hD' hN hE
  calc
    (∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖) ^ 32 ≤
        (N : ℝ) ^ 60 *
          (8 * (648 ^ 4 * (N : ℝ) ^ 4 * (D : ℝ) ^ 28 +
            1024 ^ 4 * (D : ℝ) ^ 25 * (((D' + 1 : ℕ) : ℝ) ^ 4) *
              (6 * (D : ℝ) ^ 3 * (N : ℝ) ^ 3 + 16 * (N : ℝ) * E))) := by
      exact exercise_hua_typeII_clipped_ordered_norms_thirtyTwo_le
        P l D D' a q P' b c V hD hDD' hD'
    _ ≤ (N : ℝ) ^ 60 *
        ((2 : ℝ) ^ 64 * (D : ℝ) ^ 32 * (N : ℝ) ^ 4 *
          (1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
            E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by ring

#print axioms exercise_hua_typeII_clipped_ordered_norms_normalized_le

/-- An integer-power divisor threshold suffices for the unchanged MIN-01
gates. With `T = (log P)^tau`, these strict budgets cover the rich tail,
the `P₀` spacing term and the denominator terms, respectively. -/
theorem exercise_hua_typeII_divisor_threshold_exponent_budget
    (saving sigma3 sigma6 sigma : ℕ)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma) :
    let tau := (3 * sigma3 + 64 * saving + 2052) / 5
    3 * sigma3 + 1023 + 64 * saving < 5 * tau ∧
      5 * tau + 4 * sigma3 + 1 + 64 * saving < sigma6 ∧
      5 * tau + 3 * sigma3 + 1 + 64 * saving < sigma := by
  exact hua_typeII_divisor_threshold_exponent_budget saving sigma3 sigma6 sigma h6 hsigma

#print axioms exercise_hua_typeII_divisor_threshold_exponent_budget

/-- **MIN-01, proved source estimate.** The mean-square
step underlying Hua Lemma 6.3, specialized to cubic degree and `Q=1`.

Source: the local English Hua scan, printed pp. 68--72; review §26 and §66.
Use `P₁=P/l`, not the Type-I progression-count notation. Here `P'` can be
any positive lower endpoint. The inner support is a single fixed set `V`
intersected with the variable interval; an arbitrary support depending on
`u` would make this claim false.

The finite support and differencing stages use
`exercise_hua_typeII_mean_square_le_clipped_ordered_norms` and
`exercise_hua_typeII_clipped_ordered_norms_normalized_le`. The actual three
outer/two inner differences retain the surviving support; the diagonal
terms account for zero shifts before the positive five-shift box is used.

The scalar assembly uses the actual floor `N = floor(P/(lD))`.
`hua_typeII_cubic_frequency_log_saving` bounds the positive five-shift
contribution by `Kf/(log P)^(64*saving)`, and
`hua_typeII_scalar_diagonal_log_saving` bounds the two zero-shift losses.
An oversized constant `A≥1` satisfies `A≤A^32`, so the 32nd-power estimate
gives the needed norm saving without fractional powers. The same floor
comparison absorbs the original mean-square diagonal. All thresholds are
uniform, and the exact gates `h5`, `h6`, and `hsigma` are retained.

The resulting constant may depend on these fixed exponents, never on
`P,l,D,D',P',a,q,V,b,c,d`. -/
theorem exercise_hua_typeII_mean_square
    (saving sigma3 sigma5 sigma6 sigma : ℕ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in atTop,
      ∀ l D D' a q : ℕ, ∀ P' : ℝ, ∀ V : Finset ℕ, ∀ b c d : ℝ,
        0 < l → (l : ℝ) ≤ Real.log (P : ℝ) ^ sigma3 →
        0 < P' → 0 < D → D ≤ D' → D' ≤ 2 * D →
        Real.log (P : ℝ) ^ sigma5 < D →
        (D : ℝ) < (P : ℝ) / Real.log (P : ℝ) ^ sigma6 →
        Nat.Coprime a q →
        Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        (∑ u ∈ Finset.Icc (D + 1) D',
          ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) ≤
            K * ((P : ℝ) / l) ^ 2 /
              ((D : ℝ) * Real.log (P : ℝ) ^ (2 * saving)) := by
  classical
  obtain ⟨Kf, hKf, hfrequency⟩ :=
    hua_typeII_cubic_frequency_log_saving saving sigma3 sigma6 sigma h6 hsigma
  let A : ℝ := (2 : ℝ) ^ 64 * (Kf + 3) + 1
  have hAone : 1 ≤ A := by
    have hnonneg : 0 ≤ (2 : ℝ) ^ 64 * (Kf + 3) := by positivity
    dsimp only [A]
    linarith only [hnonneg]
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hAone
  have hAbase : (2 : ℝ) ^ 64 * (Kf + 3) ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_right (by norm_num)
  refine ⟨2 + 2 * A, by positivity, ?_⟩
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (2 : ℝ)] with P hlogP
  intro l D D' a q P' V b c d hl hlupper _hP' hD hDD' hD' hDlower hDupper
    hac hqlower hqupper
  let L : ℝ := Real.log (P : ℝ)
  let P₁ : ℝ := (P : ℝ) / l
  let N : ℕ := Nat.floor (P₁ / D)
  let W := V ∩ Finset.Icc 1 N
  let S := fun v w => ∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
    generalCubicPhase
      (((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
      (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u
  let R : ℝ := ∑ w ∈ W, ∑ v ∈ W.filter (fun v => w < v), ‖S v w‖
  let E : ℝ := ∑ x ∈ huaTypeIICubicShiftBox D N,
    linearDistanceEnvelope (N : ℝ)
      (((a : ℝ) / q) * (huaTypeIICubicShiftFrequency l x : ℝ))
  change (∑ u ∈ Finset.Icc (D + 1) D',
    ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) ≤
      (2 + 2 * A) * P₁ ^ 2 / ((D : ℝ) * L ^ (2 * saving))
  have hL : 2 ≤ L := hlogP
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : 1 ≤ D := by omega
  have hP₁ : 0 ≤ P₁ := by dsimp only [P₁]; positivity
  obtain ⟨hN1, hNlog, _, hNupper⟩ :=
    hua_typeII_floor_inner_endpoint_bounds P l D sigma3 sigma6 L hl hD hL
      (by omega) hlupper hDupper
  change 1 ≤ N at hN1
  change L ^ (sigma6 - sigma3) / 2 ≤ (N : ℝ) at hNlog
  change (N : ℝ) ≤ P₁ / D at hNupper
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hscalar := hua_typeII_scalar_diagonal_log_saving
    saving sigma3 sigma5 sigma6 P l D L h5 h6 hl hD hL hlupper hDlower hDupper
  change 1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) ≤ 3 / L ^ (64 * saving) at hscalar
  have hfreq := hfrequency P l D a q hL hl hlupper hD hDupper hac hqlower hqupper
  change E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤ Kf / L ^ (64 * saving) at hfreq
  have hrate : 1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
      E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤ (Kf + 3) / L ^ (64 * saving) := by
    calc
      _ ≤ 3 / L ^ (64 * saving) + Kf / L ^ (64 * saving) := add_le_add hscalar hfreq
      _ = _ := by ring
  have hnormalized := exercise_hua_typeII_clipped_ordered_norms_normalized_le
    P l D D' a q P' b c V hD1 hDD' hD' hNpos
  change R ^ 32 ≤ (2 : ℝ) ^ 64 * (D : ℝ) ^ 32 * (N : ℝ) ^ 64 *
    (1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) +
      E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) at hnormalized
  have hRpow : R ^ 32 ≤ A * (D : ℝ) ^ 32 * (N : ℝ) ^ 64 /
      L ^ (64 * saving) := by
    calc
      _ ≤ (2 : ℝ) ^ 64 * (D : ℝ) ^ 32 * (N : ℝ) ^ 64 *
          ((Kf + 3) / L ^ (64 * saving)) :=
        hnormalized.trans (mul_le_mul_of_nonneg_left hrate (by positivity))
      _ = ((2 : ℝ) ^ 64 * (Kf + 3)) * (D : ℝ) ^ 32 * (N : ℝ) ^ 64 /
          L ^ (64 * saving) := by ring
      _ ≤ _ := by gcongr
  have hR : R ≤ A * (D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving) := by
    have hApow : A ≤ A ^ 32 := by
      simpa using pow_le_pow_right₀ hAone (show 1 ≤ 32 by norm_num)
    have hshape : ((D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving)) ^ 32 =
        (D : ℝ) ^ 32 * (N : ℝ) ^ 64 / L ^ (64 * saving) := by
      simp only [div_pow, mul_pow, ← pow_mul]
      congr 1
      ring
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by positivity)
    calc
      R ^ 32 ≤ A * ((D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving)) ^ 32 := by
        rw [hshape]
        simpa only [mul_div_assoc, mul_assoc] using hRpow
      _ ≤ A ^ 32 * ((D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving)) ^ 32 :=
        mul_le_mul_of_nonneg_right hApow (by positivity)
      _ = (A * (D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving)) ^ 32 := by
        rw [← mul_pow]
        congr 1
        ring
  have hsize : (D : ℝ) * (N : ℝ) ^ 2 ≤ P₁ ^ 2 / D := by
    calc
      _ ≤ (D : ℝ) * (P₁ / D) ^ 2 := by gcongr
      _ = _ := by field_simp [ne_of_gt hDR]
  have hRtarget : R ≤ A * P₁ ^ 2 / ((D : ℝ) * L ^ (2 * saving)) := by
    calc
      R ≤ A * (D : ℝ) * (N : ℝ) ^ 2 / L ^ (2 * saving) := hR
      _ = A * ((D : ℝ) * (N : ℝ) ^ 2) / L ^ (2 * saving) := by ring
      _ ≤ A * (P₁ ^ 2 / D) / L ^ (2 * saving) := by gcongr
      _ = _ := by ring
  have hlogScale : L ^ (2 * saving) ≤ 2 * P₁ / D := by
    calc
      L ^ (2 * saving) ≤ L ^ (sigma6 - sigma3) :=
        pow_le_pow_right₀ hLone (by omega)
      _ ≤ 2 * (N : ℝ) := by linarith only [hNlog]
      _ ≤ 2 * (P₁ / D) := mul_le_mul_of_nonneg_left hNupper (by norm_num)
      _ = _ := by ring
  have hdiag : P₁ ≤ 2 * P₁ ^ 2 / ((D : ℝ) * L ^ (2 * saving)) := by
    apply (le_div_iff₀ (mul_pos hDR (pow_pos hLpos _))).mpr
    have hscale : (D : ℝ) * L ^ (2 * saving) ≤ 2 * P₁ := by
      have h := (le_div_iff₀ hDR).mp hlogScale
      nlinarith only [h]
    calc
      P₁ * ((D : ℝ) * L ^ (2 * saving)) ≤ P₁ * (2 * P₁) :=
        mul_le_mul_of_nonneg_left hscale hP₁
      _ = _ := by ring
  have hmean := exercise_hua_typeII_mean_square_le_clipped_ordered_norms
    P l D D' a q P' b c d V hl hD hD'
  change (∑ u ∈ Finset.Icc (D + 1) D',
    ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) ≤ P₁ + 2 * R at hmean
  calc
    _ ≤ P₁ + 2 * R := hmean
    _ ≤ 2 * P₁ ^ 2 / ((D : ℝ) * L ^ (2 * saving)) +
        2 * (A * P₁ ^ 2 / ((D : ℝ) * L ^ (2 * saving))) :=
      add_le_add hdiag (mul_le_mul_of_nonneg_left hRtarget (by norm_num))
    _ = _ := by ring

#print axioms exercise_hua_typeII_mean_square

/-- **MIN-02, proved; elementary finite Cauchy--Schwarz adapter.**
Use `norm_sum_le`, the real finite Cauchy--Schwarz inequality, and
`Finset.sum_le_sum_of_subset_of_nonneg`. At most `D` integers lie in
`Icc (D+1) D'`. Square the desired inequality, cancel `D>0`, and use
`Real.sq_sqrt hK`; all factors are nonnegative. This lemma has no source
estimate hidden in its hypotheses: `hmoment` is the already-isolated
mean-square input from MIN-01. -/
theorem exercise_hua_typeII_of_mean_square
    {P l D D' a q : ℕ} {P' K L : ℝ} {U V : Finset ℕ}
    {b c d : ℝ} {saving : ℕ}
    (hl : 0 < l) (hD : 0 < D) (hD' : D' ≤ 2 * D)
    (hK : 0 ≤ K) (hL : 0 < L)
    (hU : U ⊆ Finset.Icc (D + 1) D')
    (hmoment : (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖ ^ 2) ≤
        K * ((P : ℝ) / l) ^ 2 / ((D : ℝ) * L ^ (2 * saving))) :
    ‖∑ u ∈ U, exerciseHuaTypeIIInner P l P' V a q b c d u‖ ≤
      Real.sqrt K * ((P : ℝ) / l) / L ^ saving := by
  classical
  let f (u : ℕ) : ℝ := ‖exerciseHuaTypeIIInner P l P' V a q b c d u‖
  have hcard : U.card ≤ D := by
    have hsubset := Finset.card_le_card hU
    simp only [Nat.card_Icc] at hsubset
    omega
  have hsum_nonneg : 0 ≤ ∑ u ∈ U, f u := by
    apply Finset.sum_nonneg
    intro u hu
    exact norm_nonneg _
  have hsum_sq_nonneg : 0 ≤ ∑ u ∈ U, (f u) ^ 2 := by
    apply Finset.sum_nonneg
    intro u hu
    positivity
  have hsub : (∑ u ∈ U, (f u) ^ 2) ≤
      ∑ u ∈ Finset.Icc (D + 1) D', (f u) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hU
    intro u hu _
    positivity
  have hcs : (∑ u ∈ U, f u) ^ 2 ≤
      (U.card : ℝ) * (∑ u ∈ U, (f u) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq U
      (fun _ : ℕ => (1 : ℝ)) f
    simpa using h
  have hKsqrt : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have htarget_nonneg : 0 ≤ Real.sqrt K * ((P : ℝ) / l) / L ^ saving := by
    positivity
  have hlreal : (0 : ℝ) < l := by exact_mod_cast hl
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hLpow : 0 < L ^ saving := pow_pos hL _
  have hbound_sq : (∑ u ∈ U, f u) ^ 2 ≤
      (Real.sqrt K * ((P : ℝ) / l) / L ^ saving) ^ 2 := by
    calc
      _ ≤ (U.card : ℝ) * (∑ u ∈ U, (f u) ^ 2) := hcs
      _ ≤ (D : ℝ) * (∑ u ∈ Finset.Icc (D + 1) D', (f u) ^ 2) := by
        gcongr
      _ ≤ (D : ℝ) * (K * ((P : ℝ) / l) ^ 2 /
          ((D : ℝ) * L ^ (2 * saving))) :=
        mul_le_mul_of_nonneg_left hmoment hDreal.le
      _ = _ := by
        have hden : L ^ (2 * saving) = (L ^ saving) ^ 2 := by ring
        simp only [hden, div_pow, mul_pow, hKsqrt]
        field_simp [ne_of_gt hlreal, ne_of_gt hDreal, ne_of_gt hLpow]
  have hsum_le : (∑ u ∈ U, f u) ≤
      Real.sqrt K * ((P : ℝ) / l) / L ^ saving := by
    nlinarith
  exact (norm_sum_le U _).trans hsum_le

/-- **MIN-03c, proved dyadic consumer.** The proved MIN-01
mean-square estimate gives the *actual* selected-prime block the stated
Type-II norm saving. Empty blocks cost zero; nonempty blocks obtain both
`D = 2^k` size gates from `HuaTypeIIDyadicGates`. This declaration contains
no unproved source estimate in its hypotheses or dependency cone. -/
theorem exercise_eventually_hua_source_dyadic_block_bound
    (saving sigma3 sigma5 sigma6 sigma : ℕ) (lambda₃ : ℝ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ m s parity k a q : ℕ, ∀ b c d : ℝ,
        m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))) →
        Nat.Coprime a q →
        Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        ‖∑ u ∈ huaStepNineDyadicBlock
            (primeFactorsAtLeastCutoff
              (Nat.ceil (Real.rpow (Real.log P) lambda₃))
              (huaStepEightSieveProduct P)) k,
          exerciseHuaTypeIIInner P m
            ((P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ))
            (huaStepNineFixedSupport (huaStepEightSieveProduct P)
              (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity)
            a q b c d u‖ ≤
          C * ((P : ℝ) / m) / Real.log (P : ℝ) ^ saving := by
  obtain ⟨K, hK, hmean⟩ :=
    exercise_hua_typeII_mean_square saving sigma3 sigma5 sigma6 sigma
      h5 h6 hsigma
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
  filter_upwards [hmean,
    eventually_huaStepNineDyadicBlock_source_gates sigma5 sigma6 lambda₃ hLambda,
    eventually_gt_atTop (1 : ℕ)] with P hmeanP hblockGates hP
  intro m s parity k a q b c d hm hcop hqlo hqhi
  let U : Finset ℕ := huaStepNineDyadicBlock
    (primeFactorsAtLeastCutoff
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (huaStepEightSieveProduct P)) k
  let V : Finset ℕ := huaStepNineFixedSupport
    (huaStepEightSieveProduct P)
    (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity
  have hPcast : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hLpos : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  have hmSource := huaStepNineOuterMultiplier_source_bound
    P m (sigma3 : ℝ) hP hm
  have hmpos : 0 < m := hmSource.1
  have hmle : (m : ℝ) ≤ Real.log (P : ℝ) ^ sigma3 := by
    calc
      (m : ℝ) ≤ Real.rpow (Real.log P) (sigma3 : ℝ) := hmSource.2
      _ = Real.log P ^ sigma3 := Real.rpow_natCast _ _
  have hP' : 0 < (P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ) :=
    div_pos hPcast (Real.rpow_pos_of_pos hLpos _)
  have hDpos : 0 < 2 ^ k := pow_pos (by norm_num) _
  have hD'eq : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    ring
  have hDle : 2 ^ k ≤ 2 ^ (k + 1) := by omega
  have hD'le : 2 ^ (k + 1) ≤ 2 * 2 ^ k := hD'eq.le
  by_cases hUempty : U = ∅
  · change ‖∑ u ∈ U, exerciseHuaTypeIIInner P m
        ((P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ)) V
        a q b c d u‖ ≤ _
    simp only [hUempty, Finset.sum_empty, norm_zero]
    positivity
  · obtain ⟨u, hu⟩ : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
    obtain ⟨hDlo, hDhi, _, _⟩ := hblockGates k u hu
    have hmeanSquare := hmeanP (l := m) (D := 2 ^ k)
      (D' := 2 ^ (k + 1)) (a := a) (q := q)
      (P' := (P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ))
      (V := V) (b := b) (c := c) (d := d)
      hmpos hmle hP' hDpos hDle hD'le hDlo hDhi hcop hqlo hqhi
    have hUsubset : U ⊆ Finset.Icc (2 ^ k + 1) (2 ^ (k + 1)) :=
      exercise_huaStepNineDyadicBlock_subset_typeII_interval P k lambda₃
    have hblock := exercise_hua_typeII_of_mean_square
      (P := P) (l := m) (D := 2 ^ k) (D' := 2 ^ (k + 1))
      (a := a) (q := q)
      (P' := (P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ))
      (K := K) (L := Real.log P) (U := U) (V := V)
      (b := b) (c := c) (d := d) (saving := saving)
      hmpos hDpos hD'le hK.le hLpos hUsubset hmeanSquare
    simpa only [U, V] using hblock

/-- **MIN-03d, source-dependent dyadic aggregation.** The exact `Q=1`
step-eight pair sum is bounded by the number of dyadic blocks times the
uniform MIN-01/MIN-02 block saving. The remaining source work must sum over
the fixed multiplier, count, and parity indices and absorb this logarithmic
block factor. Its MIN-01/MIN-02 inputs are proved. -/
theorem exercise_eventually_hua_source_pair_bound_modOne
    (saving sigma3 sigma5 sigma6 sigma : ℕ) (lambda₃ : ℝ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ m s parity t a q : ℕ, ∀ b c d : ℝ,
        m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))) →
        Nat.Coprime a q →
        Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        ‖∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
            (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
            (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
          generalCubicPhase ((a : ℝ) / q) b c d
            (m * (pair.1 * pair.2))‖ ≤
          C * (Nat.log 2 (Nat.sqrt P) + 1 : ℕ) * ((P : ℝ) / m) /
            Real.log (P : ℝ) ^ saving := by
  obtain ⟨C, hC, hblock⟩ :=
    exercise_eventually_hua_source_dyadic_block_bound
      saving sigma3 sigma5 sigma6 sigma lambda₃ h5 h6 hsigma hLambda
  refine ⟨C, hC, ?_⟩
  filter_upwards [hblock, eventually_gt_atTop (1 : ℕ)] with P hblockP hP
  intro m s parity t a q b c d hm hcop hqlo hqhi
  have hmpos : 0 < m := by
    exact lt_of_lt_of_le (by omega : 0 < 1) (Finset.mem_Icc.mp hm).1
  have hLpos : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  let Kset : Finset ℕ := Finset.Icc 0 (Nat.log 2 (Nat.sqrt P))
  let B : ℝ := C * ((P : ℝ) / m) / Real.log (P : ℝ) ^ saving
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  rw [exercise_sum_huaStepEightSourcePairs_eq_sum_stepNineDyadicInner_modOne
    P m t s parity a q (sigma3 : ℝ) lambda₃ b c d hmpos]
  calc
    ‖∑ k ∈ Kset,
        ∑ u ∈ huaStepNineDyadicBlock
          (primeFactorsAtLeastCutoff
            (Nat.ceil (Real.rpow (Real.log P) lambda₃))
            (huaStepEightSieveProduct P)) k,
          exerciseHuaTypeIIInner P m
            ((P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ))
            (huaStepNineFixedSupport (huaStepEightSieveProduct P)
              (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity)
            a q b c d u‖ ≤
        ∑ k ∈ Kset,
          ‖∑ u ∈ huaStepNineDyadicBlock
            (primeFactorsAtLeastCutoff
              (Nat.ceil (Real.rpow (Real.log P) lambda₃))
              (huaStepEightSieveProduct P)) k,
            exerciseHuaTypeIIInner P m
              ((P : ℝ) / Real.rpow (Real.log P) (sigma3 : ℝ))
              (huaStepNineFixedSupport (huaStepEightSieveProduct P)
                (Nat.ceil (Real.rpow (Real.log P) lambda₃)) s parity)
              a q b c d u‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Kset, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblockP m s parity k a q b c d hm hcop hqlo hqhi
    _ = C * (Nat.log 2 (Nat.sqrt P) + 1 : ℕ) * ((P : ℝ) / m) /
        Real.log (P : ℝ) ^ saving := by
      simp only [Kset, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      dsimp [B]
      ring

/-- The normalized positive-large-factor Type-II pair aggregate at source
modulus one, with a bounded outer coefficient available for the eventual
Möbius/parity assembly. -/
noncomputable def exerciseHuaTypeIIPairAggregate_modOne
    (P t parity a q sigma3 : ℕ) (lambda₃ b c d : ℝ)
    (coefficient : ℕ → ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1
      (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
    ∑ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
      coefficient m s *
        ((∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
            (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
            (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
          generalCubicPhase ((a : ℝ) / q) b c d
            (m * (pair.1 * pair.2))) / (s : ℂ))

/-- **MIN-03e, proved outer aggregation.** The proved dyadic
pair estimate is summed over the source's positive multiplier and factor-count
ranges with exact reciprocal `m` and `s` weights. The source estimate and
this finite harmonic consumer have standard-only axiom audits. -/
theorem exercise_eventually_hua_pair_aggregate_harmonic_bound_modOne
    (saving sigma3 sigma5 sigma6 sigma : ℕ) (lambda₃ : ℝ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ t parity a q : ℕ, ∀ b c d : ℝ,
        Nat.Coprime a q →
        Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        ∀ coefficient : ℕ → ℕ → ℂ,
          (∀ m ∈ Finset.Icc 1
              (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
            ∀ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
              ‖coefficient m s‖ ≤ 1) →
          ‖exerciseHuaTypeIIPairAggregate_modOne P t parity a q sigma3
            lambda₃ b c d coefficient‖ ≤
            (C * (Nat.log 2 (Nat.sqrt P) + 1 : ℕ) * (P : ℝ) /
              Real.log (P : ℝ) ^ saving) *
              (harmonic (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))) : ℝ) *
              (harmonic (Nat.floor (Real.log P)) : ℝ) := by
  obtain ⟨C, hC, hpair⟩ :=
    exercise_eventually_hua_source_pair_bound_modOne
      saving sigma3 sigma5 sigma6 sigma lambda₃ h5 h6 hsigma hLambda
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpair, eventually_gt_atTop (1 : ℕ)] with P hpairP hP
  intro t parity a q b c d hcop hqlo hqhi coefficient hcoefficient
  let M := Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))
  let S := Nat.floor (Real.log P)
  let T : ℝ := C * (Nat.log 2 (Nat.sqrt P) + 1 : ℕ) * (P : ℝ) /
    Real.log (P : ℝ) ^ saving
  change ‖∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
    coefficient m s *
      ((∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
        generalCubicPhase ((a : ℝ) / q) b c d
          (m * (pair.1 * pair.2))) / (s : ℂ))‖ ≤
      T * (harmonic M : ℝ) * (harmonic S : ℝ)
  apply norm_weighted_reciprocal_double_sum_le M S T _ coefficient hcoefficient
  intro m hm s hs
  have hmpos : 0 < m := by
    have hml := (Finset.mem_Icc.mp hm).1
    omega
  have hspos : 0 < s := by
    have hsl := (Finset.mem_Icc.mp hs).1
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hLpos : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  have hpairBound := hpairP m s parity t a q b c d hm hcop hqlo hqhi
  calc
    ‖(∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
        generalCubicPhase ((a : ℝ) / q) b c d
          (m * (pair.1 * pair.2))) / (s : ℂ)‖ =
      ‖∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
        generalCubicPhase ((a : ℝ) / q) b c d
          (m * (pair.1 * pair.2))‖ / (s : ℝ) := by simp
    _ ≤ (C * (Nat.log 2 (Nat.sqrt P) + 1 : ℕ) * ((P : ℝ) / m) /
        Real.log (P : ℝ) ^ saving) / (s : ℝ) := by
      exact div_le_div_of_nonneg_right hpairBound hsR.le
    _ = T / ((s : ℝ) * m) := by
      dsimp [T]
      field_simp [ne_of_gt hmR, ne_of_gt hsR,
        ne_of_gt (pow_pos hLpos saving)]

/-- The complete large-divisor source contribution at modulus one has the
desired logarithmic saving, including its smooth terms and repeated-prime
correction. The coarse overhead budget pays for the actual dyadic and two
harmonic factors; it imposes no bound on the phase as a new hypothesis. -/
theorem exercise_eventually_hua_source_eligible_bound_modOne
    (decay saving sigma3 sigma5 sigma6 sigma : ℕ) (lambda₃ : ℝ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma)
    (hLambda : ((sigma5 + 1 : ℕ) : ℝ) ≤ lambda₃)
    (hoverhead : decay + sigma3 + 2 ≤ saving) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ t parity a q : ℕ, ∀ b c d : ℝ,
        Nat.Coprime a q →
        Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        ‖∑ m ∈ Finset.Icc 1
            (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
          ∑ v ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
            (P / m) parity (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
            generalCubicPhase ((a : ℝ) / q) b c d (m * v)‖ ≤
          C * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
  classical
  obtain ⟨C, hC, hpair⟩ := exercise_eventually_hua_pair_aggregate_harmonic_bound_modOne
    saving sigma3 sigma5 sigma6 sigma lambda₃ h5 h6 hsigma hLambda
  have hdecay : (decay : ℝ) < lambda₃ := by
    have hnat : decay < sigma5 + 1 := by omega
    exact lt_of_lt_of_le (by exact_mod_cast hnat) hLambda
  have hLambdaPos : 0 < lambda₃ := (Nat.cast_nonneg decay).trans_lt hdecay
  obtain ⟨K, hK, herror⟩ :=
    eventually_norm_huaSourceStepEight_eligible_sub_pairs_logSaving_le
      (lambda₂ := (sigma3 : ℝ)) (rho := (decay : ℝ))
      (Nat.cast_nonneg sigma3) hLambdaPos (Nat.cast_nonneg decay) hdecay
  let J : ℝ := 1 / Real.log 2 + 1
  have hJ : 0 < J := by
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp only [J]
    positivity
  refine ⟨K + C * J, by positivity, ?_⟩
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpair, herror, hlog.eventually_ge_atTop (2 : ℝ)] with
    P hpairP herrorP hL
  intro t parity a q b c d hcop hqlo hqhi
  let A : ℂ := ∑ m ∈ Finset.Icc 1
      (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
    ∑ v ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
      (P / m) parity (huaStepEightSourceCondition P m 1 t (sigma3 : ℝ)),
      generalCubicPhase ((a : ℝ) / q) b c d (m * v)
  let B := exerciseHuaTypeIIPairAggregate_modOne P t parity a q sigma3
    lambda₃ b c d (fun _ _ => 1)
  have hB : ‖B‖ ≤ (C * J) * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    have h := hpairP t parity a q b c d hcop hqlo hqhi (fun _ _ => 1)
      (by intro m hm s hs; simp)
    exact h.trans (hua_typeII_harmonic_overhead_log_saving_le
      P sigma3 saving decay C hL hC.le hoverhead)
  have hAB : ‖A - B‖ ≤ K * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    have h := herrorP.2 1 t parity ((a : ℝ) / q) b c d
    simpa only [A, B, exerciseHuaTypeIIPairAggregate_modOne, one_mul,
      Real.rpow_eq_pow, Real.rpow_natCast] using h
  change ‖A‖ ≤ (K + C * J) * (P : ℝ) / Real.log (P : ℝ) ^ decay
  calc
    ‖A‖ = ‖(A - B) + B‖ := by congr 1; ring
    _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
    _ ≤ K * (P : ℝ) / Real.log (P : ℝ) ^ decay +
        (C * J) * (P : ℝ) / Real.log (P : ℝ) ^ decay := add_le_add hAB hB
    _ = _ := by ring

#print axioms exercise_eventually_hua_source_eligible_bound_modOne

/-- The actual quotient interval in the prime sieve is exactly the fixed
positive inner set cut by the two real product endpoints. -/
theorem exercise_hua_typeII_inner_eq_source_quotients
    (P A u a q : ℕ) (b c d : ℝ) (hu : 0 < u) :
    exerciseHuaTypeIIInner P 1 (A : ℝ) (Finset.Icc 1 P) a q b c d u =
      ∑ v ∈ Finset.Ioc (A / u) (P / u),
        generalCubicPhase ((a : ℝ) / q) b c d (u * v) := by
  classical
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hsupport : exerciseHuaTypeIIInnerSupport P 1 (A : ℝ) (Finset.Icc 1 P) u =
      Finset.Ioc (A / u) (P / u) := by
    ext v
    simp only [exerciseHuaTypeIIInnerSupport, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc, Nat.cast_one, div_one]
    constructor
    · rintro ⟨_, hvpos, hvlo, hvhi⟩
      have hlo : A < v * u := by exact_mod_cast (div_lt_iff₀ huR).mp hvlo
      have hhi : v * u ≤ P := by exact_mod_cast (le_div_iff₀ huR).mp hvhi
      exact ⟨(Nat.div_lt_iff_lt_mul hu).mpr hlo, (Nat.le_div_iff_mul_le hu).mpr hhi⟩
    · rintro ⟨hvlo, hvhi⟩
      have hvpos : 0 < v := (Nat.zero_le (A / u)).trans_lt hvlo
      have hvP : v ≤ P := hvhi.trans (Nat.div_le_self P u)
      have hlo : A < v * u := (Nat.div_lt_iff_lt_mul hu).mp hvlo
      have hhi : v * u ≤ P := (Nat.le_div_iff_mul_le hu).mp hvhi
      refine ⟨⟨hvpos, hvP⟩, hvpos, ?_, ?_⟩
      · exact (div_lt_iff₀ huR).mpr (by exact_mod_cast hlo)
      · exact (le_div_iff₀ huR).mpr (by exact_mod_cast hhi)
  simp only [exerciseHuaTypeIIInner, hsupport, one_mul]

/-- The finite Cauchy step also controls the sum of inner norms, so actual
bounded Möbius signs can be retained on a selected dyadic divisor block. -/
theorem exercise_hua_typeII_sum_norms_of_mean_square
    {P D D' a q : ℕ} {P' K L : ℝ} {U V : Finset ℕ}
    {b c d : ℝ} {saving : ℕ}
    (hD : 0 < D) (hD' : D' ≤ 2 * D) (hK : 0 ≤ K) (hL : 0 < L)
    (hU : U ⊆ Finset.Icc (D + 1) D')
    (hmoment : (∑ u ∈ Finset.Icc (D + 1) D',
      ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖ ^ 2) ≤
        K * (P : ℝ) ^ 2 / ((D : ℝ) * L ^ (2 * saving))) :
    (∑ u ∈ U, ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖) ≤
      Real.sqrt K * (P : ℝ) / L ^ saving := by
  have hcard : (U.card : ℝ) ≤ D := by
    have h := Finset.card_le_card hU
    simp only [Nat.card_Icc] at h
    exact_mod_cast (show U.card ≤ D by omega)
  have hsub : (∑ u ∈ U, ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖ ^ 2) ≤
      ∑ u ∈ Finset.Icc (D + 1) D',
        ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (by intro u hu hnot; positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ : ℕ => (1 : ℝ))
    (fun u => ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hsquare : (∑ u ∈ U, ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖) ^ 2 ≤
      (Real.sqrt K * (P : ℝ) / L ^ saving) ^ 2 := by
    calc
      _ ≤ (U.card : ℝ) *
          (∑ u ∈ U, ‖exerciseHuaTypeIIInner P 1 P' V a q b c d u‖ ^ 2) := hcs
      _ ≤ (D : ℝ) * (K * (P : ℝ) ^ 2 / ((D : ℝ) * L ^ (2 * saving))) := by
        gcongr
        exact hsub.trans hmoment
      _ = _ := by
        have hden : L ^ (2 * saving) = (L ^ saving) ^ 2 := by ring
        simp only [hden, div_pow, mul_pow, Real.sq_sqrt hK]
        field_simp [ne_of_gt hDR, ne_of_gt (pow_pos hL saving)]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hsquare

/-- The true Möbius-weighted medium-divisor branch of the prime sieve has
the desired rate. Both quotient endpoints are retained. Nonempty actual
dyadic blocks supply the source gates, and their full logarithmic count is
paid for by the saving budget. No cancellation premise is added. -/
theorem exercise_eventually_hua_medium_moebius_bound
    (decay saving sigma5 sigma6 sigma lambda1 lambda2 : ℕ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 128 * saving + 32768 ≤ sigma6)
    (hsigma : 128 * saving + 32768 < sigma)
    (hLambda1 : sigma5 + 1 ≤ lambda1) (hLambda2 : sigma6 + 1 ≤ lambda2)
    (hoverhead : decay + 2 ≤ saving) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ a q : ℕ, ∀ b c d : ℝ,
        Nat.Coprime a q → Real.log (P : ℝ) ^ sigma < q →
        (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
        ‖∑ u ∈ (huaStepEightSieveProduct P).divisors.filter (fun u : ℕ =>
            Real.log (P : ℝ) ^ lambda1 < (u : ℝ) ∧
            (u : ℝ) ≤ (P : ℝ) / Real.log (P : ℝ) ^ lambda2),
          (ArithmeticFunction.moebius u : ℂ) *
            ∑ v ∈ Finset.Ioc (Nat.sqrt P / u) (P / u),
              generalCubicPhase ((a : ℝ) / q) b c d (u * v)‖ ≤
          C * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
  classical
  obtain ⟨K, hK, hmean⟩ := exercise_hua_typeII_mean_square
    saving 0 sigma5 sigma6 sigma h5 (by simpa using h6) (by simpa using hsigma)
  let J : ℝ := 1 / Real.log 2 + 1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hJ : 0 < J := by dsimp only [J]; positivity
  refine ⟨Real.sqrt K * J, by positivity, ?_⟩
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmean, eventually_huaTypeII_lowerDyadicGate sigma5 (lambda1 : ℝ)
    (by exact_mod_cast hLambda1), hlog.eventually_ge_atTop (2 : ℝ),
    eventually_gt_atTop (1 : ℕ)] with P hmeanP hcut hL hP
  intro a q b c d hcop hqlo hqhi
  let L : ℝ := Real.log (P : ℝ)
  let S := (huaStepEightSieveProduct P).divisors.filter (fun u : ℕ =>
    L ^ lambda1 < (u : ℝ) ∧ (u : ℝ) ≤ (P : ℝ) / L ^ lambda2)
  let f := fun u => (ArithmeticFunction.moebius u : ℂ) *
    ∑ v ∈ Finset.Ioc (Nat.sqrt P / u) (P / u),
      generalCubicPhase ((a : ℝ) / q) b c d (u * v)
  change ‖∑ u ∈ S, f u‖ ≤ (Real.sqrt K * J) * (P : ℝ) / L ^ decay
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hroot : (0 : ℝ) < Nat.sqrt P := by
    exact_mod_cast Nat.sqrt_pos.mpr (by omega : 0 < P)
  have hSbounds (u : ℕ) (hu : u ∈ S) : 2 ≤ u ∧ u ≤ P := by
    have hs := (Finset.mem_filter.mp hu).2
    have hone : 1 ≤ L ^ lambda1 := one_le_pow₀ hLone
    have huR : (1 : ℝ) < u := hone.trans_lt hs.1
    have hupper : (u : ℝ) ≤ P := hs.2.trans
      (div_le_self hPR.le (one_le_pow₀ hLone))
    exact ⟨by exact_mod_cast huR, by exact_mod_cast hupper⟩
  have hblocks (k : ℕ) : ‖∑ u ∈ huaStepNineDyadicBlock S k, f u‖ ≤
      Real.sqrt K * (P : ℝ) / L ^ saving := by
    let U := huaStepNineDyadicBlock S k
    by_cases hempty : U = ∅
    · change ‖∑ u ∈ U, f u‖ ≤ _
      simp only [hempty, Finset.sum_empty, norm_zero]
      positivity
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have huS := (Finset.mem_filter.mp hu).1
    obtain ⟨hDu, huhi⟩ := mem_huaStepNineDyadicBlock_imp hu (hSbounds u huS).1
    have huhi' : (u : ℝ) ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [pow_succ, mul_comm] using huhi)
    have hDuR : ((2 ^ k : ℕ) : ℝ) < u := by exact_mod_cast hDu
    have hDlo : L ^ sigma5 < ((2 ^ k : ℕ) : ℝ) := by
      have hcut' : 2 * L ^ sigma5 < L ^ lambda1 := by
        simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hcut
      have hs := (Finset.mem_filter.mp huS).2.1
      linarith only [hcut', hs, huhi']
    have hDhi : ((2 ^ k : ℕ) : ℝ) < (P : ℝ) / L ^ sigma6 := by
      apply hDuR.trans_le
      apply ((Finset.mem_filter.mp huS).2.2).trans
      exact div_le_div_of_nonneg_left hPR.le (pow_pos hLpos _) 
        (pow_le_pow_right₀ hLone (by omega : sigma6 ≤ lambda2))
    have hU : U ⊆ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k) := by
      intro v hv
      have hvS := (Finset.mem_filter.mp hv).1
      obtain ⟨hlo, hhi⟩ := mem_huaStepNineDyadicBlock_imp hv (hSbounds v hvS).1
      exact Finset.mem_Icc.mpr ⟨by omega, by simpa [pow_succ, mul_comm] using hhi⟩
    have hmoment := hmeanP 1 (2 ^ k) (2 * 2 ^ k) a q (Nat.sqrt P : ℝ)
      (Finset.Icc 1 P) b c d (by norm_num) (by simp) hroot
      (by positivity) (by omega) le_rfl hDlo hDhi hcop hqlo hqhi
    simp only [Nat.cast_one, div_one] at hmoment
    have hnorms := exercise_hua_typeII_sum_norms_of_mean_square
      (saving := saving) (by positivity : 0 < 2 ^ k) le_rfl hK.le hLpos hU hmoment
    calc
      ‖∑ v ∈ U, f v‖ ≤ ∑ v ∈ U, ‖f v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ U,
          ‖exerciseHuaTypeIIInner P 1 (Nat.sqrt P : ℝ) (Finset.Icc 1 P) a q b c d v‖ := by
        apply Finset.sum_le_sum
        intro v hv
        have hvpos : 0 < v := by have := (hSbounds v (Finset.mem_filter.mp hv).1).1; omega
        have hmu : ‖(ArithmeticFunction.moebius v : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := v)
        dsimp only [f]
        rw [← exercise_hua_typeII_inner_eq_source_quotients P (Nat.sqrt P) v a q b c d hvpos,
          norm_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu
          (norm_nonneg (exerciseHuaTypeIIInner P 1 (Nat.sqrt P : ℝ) (Finset.Icc 1 P) a q b c d v))
      _ ≤ _ := hnorms
  have hcount : ((Nat.log 2 P + 1 : ℕ) : ℝ) ≤ J * L := by
    have hpow : (2 : ℝ) ^ Nat.log 2 P ≤ P := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : P ≠ 0)
    have hlogNat := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    rw [Real.log_pow] at hlogNat
    have hlogBound : (Nat.log 2 P : ℝ) ≤ L / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hlogNat
    calc
      _ ≤ L / Real.log 2 + 1 := by push_cast; linarith only [hlogBound]
      _ ≤ L / Real.log 2 + L := add_le_add le_rfl hLone
      _ = _ := by dsimp only [J]; ring
  calc
    ‖∑ u ∈ S, f u‖ = ‖∑ k ∈ Finset.Icc 0 (Nat.log 2 P),
        ∑ u ∈ huaStepNineDyadicBlock S k, f u‖ := by
      rw [sum_eq_sum_huaStepNineDyadicBlocks f (fun u hu => (hSbounds u hu).2)]
    _ ≤ ∑ k ∈ Finset.Icc 0 (Nat.log 2 P),
        ‖∑ u ∈ huaStepNineDyadicBlock S k, f u‖ := norm_sum_le _ _
    _ ≤ ((Nat.log 2 P + 1 : ℕ) : ℝ) * (Real.sqrt K * (P : ℝ) / L ^ saving) := by
      exact (Finset.sum_le_sum (fun k hk => hblocks k)).trans_eq (by simp [Nat.card_Icc])
    _ ≤ (J * L) * (Real.sqrt K * (P : ℝ) / L ^ saving) := by gcongr
    _ = (Real.sqrt K * J) * (P : ℝ) * L / L ^ saving := by ring
    _ ≤ (Real.sqrt K * J) * (P : ℝ) * L / L ^ (decay + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hLpos _)
        (pow_le_pow_right₀ hLone (by omega : decay + 1 ≤ saving))
    _ = _ := by rw [pow_succ]; field_simp [ne_of_gt hLpos]

#print axioms exercise_hua_typeII_inner_eq_source_quotients
#print axioms exercise_hua_typeII_sum_norms_of_mean_square
#print axioms exercise_eventually_hua_medium_moebius_bound

/-- Unweighted prime sum for a cubic polynomial with arbitrary real lower
coefficients. The zero endpoint contributes zero. -/
noncomputable def exerciseGeneralCubicPrimeSum (a q : ℕ)
    (b c d : ℝ) (P : ℕ) : ℂ := by
  classical
  exact ∑ p ∈ Finset.Icc 0 P,
    if p.Prime then generalCubicPhase ((a : ℝ) / q) b c d p else 0

/-- Named source contract: eventual rational-leading prime cancellation,
uniform in the reduced numerator, denominator, and all lower coefficients. -/
def ExerciseRationalPrimeSaving (E decay : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ P : ℕ in atTop, ∀ a q : ℕ, ∀ b c d : ℝ,
    Nat.Coprime a q →
    Real.log ((P : ℝ) + 2) ^ E < q →
    (q : ℝ) < (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ E →
    ‖exerciseGeneralCubicPrimeSum a q b c d P‖ ≤
      C * (P : ℝ) / Real.log ((P : ℝ) + 2) ^ decay

/-- **MIN-03, proved Hua Theorem 10 assembly.** The exact Möbius sieve is
split into small, medium and large divisor ranges. Small divisors subtract
two coefficient-uniform Type-I prefixes; medium divisors use MIN-01 on
the actual dyadic blocks with lower endpoint `sqrt(P)`; large divisors
are reindexed into the proved even-minus-odd source aggregates. Both
quotient endpoints and all signs are retained until their removal is
justified. Fixed exponent budgets pay every finite overhead, absorb the
square-root remainder and transfer the rate to `log(P+2)`. Source: Hua,
printed pp. 66 and 73--77. No optimal exponent is asserted. -/
theorem exercise_rational_prime_log_saving (decay : ℕ) :
    ∃ E : ℕ, 0 < E ∧ ∃ C : ℝ, 0 < C ∧
      ExerciseRationalPrimeSaving E decay C := by
  classical
  -- Generous fixed exponents pay for every actual finite source loss.
  let SM := decay + 2
  let lambda1 := 64 * SM + 1
  let lambda2 := 128 * SM + 32769
  let TI := decay + lambda1 + 1
  let sigma0 := 3 * (lambda1 + 2) + 20 * TI
  let SL := decay + lambda2 + 2
  let E := 8 * (sigma0 + lambda1) + 8 +
    (6 * lambda2 + 128 * SL + 32769) + (128 * SM + 32769)
  have hTypeI : 8 * (sigma0 + lambda1) + 8 ≤ E := by dsimp only [E]; omega
  have hMedium : 128 * SM + 32768 < E := by dsimp only [E]; omega
  have hLarge : 6 * lambda2 + 128 * SL + 32768 < E := by
    dsimp only [E]
    clear hTypeI hMedium
    clear_value SM lambda1 lambda2 TI sigma0 SL E
    omega
  have hsmall := eventually_hua_prime_smallDivisors_generalCubic_logSaving_le
    E sigma0 lambda1 TI decay hTypeI
    (Nat.succ_le_succ (Nat.zero_le (decay + lambda1))) le_rfl
    (Nat.le_add_right (decay + lambda1) 1)
  obtain ⟨CM, hCM, hmedium⟩ := exercise_eventually_hua_medium_moebius_bound
    decay SM (64 * SM) (128 * SM + 32768) E lambda1 lambda2 le_rfl le_rfl
    hMedium le_rfl (by simp only [lambda2, Nat.add_assoc]; exact le_rfl) le_rfl
  obtain ⟨CL, hCL, hlarge⟩ := exercise_eventually_hua_source_eligible_bound_modOne
    decay SL lambda2 (64 * SL) (7 * lambda2 + 128 * SL + 32768) E
    ((64 * SL + 1 : ℕ) : ℝ) le_rfl le_rfl hLarge
    (by norm_num) le_rfl
  let CS : ℝ := 7612932 * (2 : ℝ) ^ TI
  let C : ℝ := 1 + CS + CM + 2 * CL
  have hCS : 0 < CS := by dsimp only [CS]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨E, (Nat.zero_le _).trans_lt hLarge,
    (2 : ℝ) ^ decay * C, by positivity, ?_⟩
  unfold ExerciseRationalPrimeSaving
  filter_upwards [hsmall, hmedium, hlarge,
    eventually_hua_divisor_cutoffs_ordered lambda1 lambda2,
    eventually_hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd lambda2,
    eventually_natSqrt_le_scale_div_log_pow decay,
    eventually_ge_atTop (2 : ℕ)] with P hsmallP hmediumP hlargeP hcutoffs
      hsourceP hroot hP
  intro a q b c d hcop hqlo hqhi
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hL : 0 < Real.log (P : ℝ) := hcutoffs.1
  have hlog : Real.log (P : ℝ) ≤ Real.log ((P : ℝ) + 2) :=
    Real.log_le_log hPpos (by linarith)
  have hlogpow : Real.log (P : ℝ) ^ E ≤ Real.log ((P : ℝ) + 2) ^ E :=
    pow_le_pow_left₀ hL.le hlog E
  have hqlo' : Real.log (P : ℝ) ^ E < q := hlogpow.trans_lt hqlo
  have hqhi' : (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ E :=
    hqhi.trans_le (div_le_div_of_nonneg_left (by positivity)
      (pow_pos hL E) hlogpow)
  let F := generalCubicPhase ((a : ℝ) / q) b c d
  let R : ℂ := ∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then F n else 0
  let S : ℂ := ∑ u ∈ (huaStepEightSieveProduct P).divisors.filter
      (fun u : ℕ => (u : ℝ) ≤ Real.log (P : ℝ) ^ lambda1),
    (ArithmeticFunction.moebius u : ℂ) *
      ∑ v ∈ Finset.Ioc (Nat.sqrt P / u) (P / u), F (u * v)
  let M : ℂ := ∑ u ∈ (huaStepEightSieveProduct P).divisors.filter
      (fun u : ℕ => Real.log (P : ℝ) ^ lambda1 < (u : ℝ) ∧
        (u : ℝ) ≤ (P : ℝ) / Real.log (P : ℝ) ^ lambda2),
    (ArithmeticFunction.moebius u : ℂ) *
      ∑ v ∈ Finset.Ioc (Nat.sqrt P / u) (P / u), F (u * v)
  let G : ℂ := ∑ u ∈ (huaStepEightSieveProduct P).divisors.filter
      (fun u : ℕ => (P : ℝ) / Real.log (P : ℝ) ^ lambda2 < (u : ℝ)),
    (ArithmeticFunction.moebius u : ℂ) *
      ∑ v ∈ Finset.Ioc (Nat.sqrt P / u) (P / u), F (u * v)
  have hdecomp : exerciseGeneralCubicPrimeSum a q b c d P = R + S + M + G := by
    exact hua_primePhase_eq_smallRemainder_add_three_divisor_ranges
      P lambda1 lambda2 F hcutoffs.2
  have hR : ‖R‖ ≤ (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    exact (hua_primePhase_smallRemainder_norm_le_sqrt P F
      (by intro n; simp only [F, norm_generalCubicPhase, le_refl])).trans hroot.2
  have hS : ‖S‖ ≤ CS * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    simpa only [S, F, CS, Real.rpow_eq_pow, Real.rpow_natCast] using
      hsmallP a q hcop hqlo hqhi.le b c d
  have hM : ‖M‖ ≤ CM * (P : ℝ) / Real.log (P : ℝ) ^ decay :=
    hmediumP a q b c d hcop hqlo' hqhi'
  have hG : ‖G‖ ≤ (2 * CL) * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    dsimp only [G]
    rw [hsourceP F]
    have heven := hlargeP 0 0 a q b c d hcop hqlo' hqhi'
    have hodd := hlargeP 0 1 a q b c d hcop hqlo' hqhi'
    exact (norm_sub_le _ _).trans ((add_le_add heven hodd).trans_eq (by ring))
  have htotal : ‖exerciseGeneralCubicPrimeSum a q b c d P‖ ≤
      C * (P : ℝ) / Real.log (P : ℝ) ^ decay := by
    rw [hdecomp]
    calc
      ‖R + S + M + G‖ ≤ ‖R + S + M‖ + ‖G‖ := norm_add_le _ _
      _ ≤ (‖R + S‖ + ‖M‖) + ‖G‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖R‖ + ‖S‖) + ‖M‖) + ‖G‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((P : ℝ) / Real.log (P : ℝ) ^ decay +
          CS * P / Real.log (P : ℝ) ^ decay) +
          CM * P / Real.log (P : ℝ) ^ decay) +
          (2 * CL) * P / Real.log (P : ℝ) ^ decay :=
        add_le_add (add_le_add (add_le_add hR hS) hM) hG
      _ = _ := by dsimp only [C]; ring
  exact htotal.trans (hua_log_rate_le_shifted_log_rate P decay C hP hC.le)

#print axioms exercise_rational_prime_log_saving

/-- Target-free odd-prime sum; isolating the prime `2` makes the existing
proper-prime-power mass bound directly reusable. -/
noncomputable def exerciseOddPrimeExpSum (alpha : ℝ) (N : ℕ) : ℂ := by
  classical
  exact ∑ k ∈ Finset.Icc 0 N,
    if IsOddPrime k then addChar alpha (primeCubic k) else 0

/-- A cutoff with explicit slack for transferring the rational theorem to
every partial endpoint. This is not a claimed optimal exponent. -/
def exerciseMinorCutoffExponent (E decay : ℕ) : ℕ :=
  2 * E + 6 * (decay + 2) + 10

theorem exerciseMinorCutoffExponent_pos (E decay : ℕ) :
    0 < exerciseMinorCutoffExponent E decay := by
  unfold exerciseMinorCutoffExponent
  omega

/-- **MIN-04a, proved; elementary logarithm and threshold exercise.**
For large endpoints `M≥N/log(N+2)^(decay+1)`, one source threshold `N₀`
works simultaneously for all `M`, and the endpoint logarithm is at least
half the ambient logarithm. The proof first uses
`isLittleO_log_rpow_rpow_atTop` to make the fixed logarithmic power at most
`sqrt N / 2`. Thus every eligible `M` exceeds `2*sqrt N`, uniformly in
`M`. The same square-root comparison proves both conclusions, and the
additive shift `2` only increases the endpoint logarithm. -/
theorem exercise_eventually_large_endpoint_log_comparison (decay N₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, M ≤ N →
      (N : ℝ) / Real.log ((N : ℝ) + 2) ^ (decay + 1) ≤ M →
        N₀ ≤ M ∧
          Real.log ((N : ℝ) + 2) / 2 ≤ Real.log ((M : ℝ) + 2) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlo : (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ (decay + 1)) =o[atTop]
      (fun N : ℕ => ((N : ℝ) + 2) ^ (1 / 2 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ))
        ((decay + 1 : ℕ) : ℝ) (by norm_num)).comp_tendsto harg
  filter_upwards [hlo.bound (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_ge_atTop (max 1 (N₀ ^ 2) : ℕ)] with N hlog hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN₀sq : N₀ ^ 2 ≤ N := (le_max_right _ _).trans hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL : 0 < Real.log ((N : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hLpow : 0 < Real.log ((N : ℝ) + 2) ^ (decay + 1) := pow_pos hL _
  have hrootSq : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hrootShiftSq : (Real.sqrt ((N : ℝ) + 2)) ^ 2 = (N : ℝ) + 2 :=
    Real.sq_sqrt (by positivity)
  have hroot : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hrootShiftNonneg : 0 ≤ Real.sqrt ((N : ℝ) + 2) := Real.sqrt_nonneg _
  have hrootShift : Real.sqrt ((N : ℝ) + 2) ≤ 2 * Real.sqrt N := by
    nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 2) - 2 * Real.sqrt N)]
  have hpowNonneg : 0 ≤ ((N : ℝ) + 2) ^ (1 / 2 : ℝ) := by positivity
  have hlog' : Real.log ((N : ℝ) + 2) ^ (decay + 1) ≤
      (1 / 4 : ℝ) * Real.sqrt ((N : ℝ) + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLpow.le,
      abs_of_nonneg hpowNonneg, one_mul, Real.sqrt_eq_rpow] using hlog
  have hLroot : Real.log ((N : ℝ) + 2) ^ (decay + 1) ≤
      Real.sqrt N / 2 := by
    linarith
  have hscale : 2 * Real.sqrt N ≤
      (N : ℝ) / Real.log ((N : ℝ) + 2) ^ (decay + 1) := by
    apply (le_div_iff₀ hLpow).2
    nlinarith [mul_le_mul_of_nonneg_left hLroot (show 0 ≤ 2 * Real.sqrt N by positivity)]
  intro M _hMN hM
  have hMroot : 2 * Real.sqrt N ≤ (M : ℝ) := hscale.trans hM
  have hN₀real : (N₀ : ℝ) ≤ Real.sqrt N := by
    have hN₀sqreal : (N₀ : ℝ) ^ 2 ≤ N := by exact_mod_cast hN₀sq
    nlinarith
  constructor
  · exact_mod_cast (show (N₀ : ℝ) ≤ M by linarith)
  · rw [← Real.log_sqrt (by positivity : 0 ≤ (N : ℝ) + 2)]
    exact Real.log_le_log (by positivity) (by linarith)

/-- **MIN-04b, proved; elementary denominator-window exercise.**
Set `L=log(N+2)` and `A=exerciseMinorCutoffExponent E decay`.
Use `eventually_log_pow_le_logarithmicDenominatorCutoff` with strict slack
to obtain `L^E<Q_A(N)` and `3*L^(E+3*(decay+1))<Q_A(N)` eventually.
The upper logarithm satisfies `log(M+2)≤L`, while
`M^3≥N^3/L^(3*(decay+1))`. Clear positive denominators, using `div_pow`
and `pow_mul`. The source window is strict: the retained slack absorbs
the factor three in the Dirichlet witness. No estimates on prime sums
enter this lemma. -/
theorem exercise_eventually_large_endpoint_denominator_window (E decay : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M q : ℕ, M ≤ N →
      (N : ℝ) / Real.log ((N : ℝ) + 2) ^ (decay + 1) ≤ M →
      logarithmicDenominatorCutoff (exerciseMinorCutoffExponent E decay) N < q →
      (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 /
        (logarithmicDenominatorCutoff (exerciseMinorCutoffExponent E decay) N : ℝ) →
      Real.log ((M : ℝ) + 2) ^ E < q ∧
        (q : ℝ) < (M : ℝ) ^ 3 / Real.log ((M : ℝ) + 2) ^ E := by
  let A := exerciseMinorCutoffExponent E decay
  let K := E + 3 * (decay + 1)
  have hAK : K + 2 < A := by
    dsimp [A, K, exerciseMinorCutoffExponent]
    omega
  have hQevent := eventually_three_mul_log_pow_le_logarithmicDenominatorCutoff
    A (K + 1) (by omega : K + 1 + 1 < A)
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlogevent := (Real.tendsto_log_atTop.comp harg).eventually_ge_atTop (2 : ℝ)
  filter_upwards [hQevent, hlogevent, eventually_ge_atTop (1 : ℕ)]
    with N hQbound hLtwo hN
  simp only [Function.comp_def] at hLtwo
  let L : ℝ := Real.log ((N : ℝ) + 2)
  have hL : 1 < L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hQstrict : 3 * L ^ K < (logarithmicDenominatorCutoff A N : ℝ) := by
    have hpowpos : 0 < L ^ K := pow_pos hLpos _
    have hpowlt : L ^ K < L ^ (K + 1) := by
      rw [pow_succ]
      nlinarith [mul_pos hpowpos (sub_pos.mpr hL)]
    change 3 * L ^ (K + 1) ≤ _ at hQbound
    exact (mul_lt_mul_of_pos_left hpowlt (by norm_num : (0 : ℝ) < 3)).trans_le hQbound
  have hQpos : 0 < (logarithmicDenominatorCutoff A N : ℝ) := by
    have : 0 < L ^ K := pow_pos hLpos _
    linarith
  intro M q hMN hMlarge hqlo hqhi
  have hMr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hlogMpos : 0 < Real.log ((M : ℝ) + 2) :=
    Real.log_pos (by
      have hMnonneg : (0 : ℝ) ≤ M := by positivity
      linarith)
  have hlogMle : Real.log ((M : ℝ) + 2) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogMpow : Real.log ((M : ℝ) + 2) ^ E ≤ L ^ E :=
    pow_le_pow_left₀ hlogMpos.le hlogMle E
  have hqloReal : (logarithmicDenominatorCutoff A N : ℝ) < q := by
    exact_mod_cast hqlo
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le hQpos hqloReal.le
  have hLepos : 0 < L ^ (decay + 1) := pow_pos hLpos _
  have hNscale : (N : ℝ) ≤ (M : ℝ) * L ^ (decay + 1) :=
    (div_le_iff₀ hLepos).mp hMlarge
  have hNcube : (N : ℝ) ^ 3 ≤ (M : ℝ) ^ 3 * (L ^ (decay + 1)) ^ 3 := by
    have h := pow_le_pow_left₀ hNpos.le hNscale 3
    simpa only [mul_pow] using h
  have hQcross : (q : ℝ) * (logarithmicDenominatorCutoff A N : ℝ) ≤
      3 * (N : ℝ) ^ 3 := (le_div_iff₀ hQpos).mp hqhi
  have hqK : (q : ℝ) * L ^ K < (N : ℝ) ^ 3 := by
    have hstrict := mul_lt_mul_of_pos_left hQstrict hqpos
    nlinarith
  have hpower : L ^ K = L ^ E * (L ^ (decay + 1)) ^ 3 := by
    have hK : K = E + (decay + 1) * 3 := by dsimp [K]; omega
    rw [hK, pow_add, pow_mul]
  have hqmain : (q : ℝ) * L ^ E < (M : ℝ) ^ 3 := by
    apply lt_of_mul_lt_mul_right _ (pow_pos hLepos 3).le
    calc
      ((q : ℝ) * L ^ E) * (L ^ (decay + 1)) ^ 3 = (q : ℝ) * L ^ K := by
        rw [hpower]
        ring
      _ < (N : ℝ) ^ 3 := hqK
      _ ≤ (M : ℝ) ^ 3 * (L ^ (decay + 1)) ^ 3 := hNcube
  constructor
  · calc
      Real.log ((M : ℝ) + 2) ^ E ≤ L ^ E := hlogMpow
      _ ≤ L ^ K := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by dsimp [K]; omega)
      _ < 3 * L ^ K := by have := pow_pos hLpos K; linarith
      _ < (logarithmicDenominatorCutoff A N : ℝ) := hQstrict
      _ < q := hqloReal
  · apply (lt_div_iff₀ (pow_pos hlogMpos E)).2
    exact (mul_le_mul_of_nonneg_left hlogMpow hqpos.le).trans_lt hqmain

/-- **MIN-04c, proved.** The short-endpoint branch needs only a term count;
it never invokes a source theorem below that theorem's threshold. -/
theorem exercise_oddPrime_prefix_trivial (alpha : ℝ) (N : ℕ) :
    ‖exerciseOddPrimeExpSum alpha N‖ ≤ (N : ℝ) + 1 := by
  classical
  unfold exerciseOddPrimeExpSum
  calc
    _ ≤ ∑ k ∈ Finset.Icc 0 N,
        ‖if IsOddPrime k then addChar alpha (primeCubic k) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 0 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> simp
    _ = (N : ℝ) + 1 := by simp

/-- The one endpoint-independent numerical gate needed by both prefix
branches: the ambient scale absorbs any fixed logarithmic power. -/
private theorem exercise_eventually_prefix_numerical_gate (decay : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log ((N : ℝ) + 2) ∧
        1 ≤ (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp harg).eventually_ge_atTop (1 : ℝ)
  have hlo : (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ decay) =o[atTop]
      (fun N : ℕ => (N : ℝ) + 2) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (decay : ℝ)
        (by norm_num)).comp_tendsto harg
  filter_upwards [hlog, hlo.bound (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (2 : ℕ)] with N hL hbound hN
  simp only [Function.comp_def] at hL
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hLpow : 0 < Real.log ((N : ℝ) + 2) ^ decay := pow_pos (by linarith) _
  have hpowBound : Real.log ((N : ℝ) + 2) ^ decay ≤
      (1 / 2 : ℝ) * ((N : ℝ) + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLpow.le,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) + 2)] using hbound
  refine ⟨hL, (le_div_iff₀ hLpow).2 ?_⟩
  linarith

/-- Exact finite removal of the exceptional even prime from the source's
all-prime cubic sum. -/
private theorem exercise_generalCubicPrimeSum_eq_oddPrime_add_two
    (a q M : ℕ) :
    exerciseGeneralCubicPrimeSum a q 0 (-((a : ℝ) / q)) 0 M =
      exerciseOddPrimeExpSum (rationalCenter a q) M +
        (if 2 ≤ M then addChar (rationalCenter a q) (primeCubic 2) else 0) := by
  classical
  unfold exerciseGeneralCubicPrimeSum exerciseOddPrimeExpSum
  have hphase (k : ℕ) :
      generalCubicPhase ((a : ℝ) / q) 0 (-((a : ℝ) / q)) 0 k =
        addChar (rationalCenter a q) (primeCubic k) := by
    simpa only [rationalCenter] using
      (addChar_primeCubic_eq_generalCubicPhase ((a : ℝ) / q) k).symm
  simp_rw [hphase]
  have hsplit :
      (∑ k ∈ Finset.Icc 0 M,
        (if k.Prime then addChar (rationalCenter a q) (primeCubic k) else 0)) =
      ∑ k ∈ Finset.Icc 0 M,
        ((if IsOddPrime k then addChar (rationalCenter a q) (primeCubic k) else 0) +
          (if k = 2 then addChar (rationalCenter a q) (primeCubic k) else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk2 : k = 2
    · subst k
      simp [IsOddPrime, Nat.prime_two]
    · by_cases hkp : k.Prime
      · simp [IsOddPrime, hkp, hk2]
      · simp [IsOddPrime, hkp, hk2]
  rw [hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_Icc]

/-- **MIN-04, proved; intermediate endpoint and logarithm exercise.**
Input is MIN-03's source theorem. Output has one rational approximant for
all partial endpoints; the constant `K` is independent of `alpha,N,M`.

1. Put `A=exerciseMinorCutoffExponent E decay` and obtain Weyl data from
   `eventually_exists_logarithmicPrimeMinorArcWeylData A`.
2. Split natural endpoints at `M₀=N/log(N+2)^(decay+1)`. For `M<M₀` bound
   the prime sum by `M+1` using `norm_sum_le`; the logarithmic extra power
   absorbs the endpoint `1` and the removed prime `2`.
3. For `M≥M₀`, call the proved
   `exercise_eventually_large_endpoint_log_comparison decay N₀`; its first
   component places every such `M` past the source threshold, and its
   second component gives `log(M+2)≥log(N+2)/2`.
4. Call the proved `exercise_eventually_large_endpoint_denominator_window`
   with the Weyl witness bounds. It places the same `q` in the strict source
   window `log(M+2)^E<q<M^3/log(M+2)^E` for every large endpoint.
5. Invoke `hsource` at endpoint `M`, with lower coefficients
   `b=0,c=-(a:ℝ)/q,d=0`. Rewrite using
   `addChar_primeCubic_eq_generalCubicPhase`; removing prime `2` costs at
   most `1`. Enlarge one constant `K` for both endpoint branches.

Use `filter_upwards` to combine thresholds before introducing `alpha,M`.
The threshold MUST NOT depend on the approximant or endpoint. -/
theorem exercise_rational_prime_prefixes
    {E decay : ℕ} {C : ℝ} (hE : 0 < E) (hC : 0 < C)
    (hsource : ExerciseRationalPrimeSaving E decay C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ alpha ∈ minorArcs N
          (logarithmicDenominatorCutoff (exerciseMinorCutoffExponent E decay) N),
        ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
          alpha = rationalCenter a q + beta + z ∧
          (N : ℝ) ^ 3 * |beta| ≤ 1 ∧
          ∀ M : ℕ, M ≤ N →
            ‖exerciseOddPrimeExpSum (rationalCenter a q) M‖ ≤
              K * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
  have _hE : E ≠ 0 := Nat.ne_of_gt hE
  obtain ⟨N₀, hsourceN₀⟩ := eventually_atTop.1 hsource
  have hlogs := exercise_eventually_large_endpoint_log_comparison decay N₀
  have hwindows := exercise_eventually_large_endpoint_denominator_window E decay
  have hweyl := eventually_exists_logarithmicPrimeMinorArcWeylData
    (exerciseMinorCutoffExponent E decay) (exerciseMinorCutoffExponent_pos _ _)
  refine ⟨C * (2 : ℝ) ^ decay + 3, by positivity, ?_⟩
  filter_upwards [hlogs, hwindows, hweyl,
    exercise_eventually_prefix_numerical_gate decay]
    with N hlogsN hwindowsN hweylN hnumN
  obtain ⟨hLone, hNdivone⟩ := hnumN
  let L : ℝ := Real.log ((N : ℝ) + 2)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLpow : 0 < L ^ decay := pow_pos hLpos _
  have hLsuc : 0 < L ^ (decay + 1) := pow_pos hLpos _
  intro alpha hminor
  obtain ⟨a, q, beta, z, hqlo, hqhi, ha, hac, happrox, hbeta,
    hscaled, hscaledOne⟩ := hweylN alpha hminor
  refine ⟨a, q, beta, z, happrox, hscaledOne, ?_⟩
  intro M hMN
  by_cases hshort : (M : ℝ) <
      (N : ℝ) / Real.log ((N : ℝ) + 2) ^ (decay + 1)
  · have hNnonneg : (0 : ℝ) ≤ N := by positivity
    have hden : L ^ decay ≤ L ^ (decay + 1) :=
      pow_le_pow_right₀ hLone (by omega)
    have hdiv : (N : ℝ) / L ^ (decay + 1) ≤ (N : ℝ) / L ^ decay :=
      div_le_div_of_nonneg_left hNnonneg hLpow hden
    have hMbound : (M : ℝ) + 1 ≤ 2 * ((N : ℝ) / L ^ decay) := by
      dsimp [L] at hdiv
      linarith
    calc
      ‖exerciseOddPrimeExpSum (rationalCenter a q) M‖ ≤ (M : ℝ) + 1 :=
        exercise_oddPrime_prefix_trivial _ _
      _ ≤ 2 * ((N : ℝ) / L ^ decay) := hMbound
      _ ≤ (C * (2 : ℝ) ^ decay + 3) * ((N : ℝ) / L ^ decay) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : 0 ≤ C * (2 : ℝ) ^ decay := by positivity
        linarith
      _ = (C * (2 : ℝ) ^ decay + 3) * (N : ℝ) /
          Real.log ((N : ℝ) + 2) ^ decay := by dsimp [L]; ring
  · have hlarge := le_of_not_gt hshort
    obtain ⟨hMsource, hMlog⟩ := hlogsN M hMN hlarge
    obtain ⟨hqsourceLo, hqsourceHi⟩ := hwindowsN M q hMN hlarge hqlo hqhi
    have hprime := hsourceN₀ M hMsource a q 0 (-((a : ℝ) / q)) 0
      hac hqsourceLo hqsourceHi
    let Lm : ℝ := Real.log ((M : ℝ) + 2)
    have hLmpos : 0 < Lm := by
      dsimp [Lm]
      have hMnonneg : (0 : ℝ) ≤ M := by positivity
      exact Real.log_pos (by linarith)
    have hLmPow : 0 < Lm ^ decay := pow_pos hLmpos _
    have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hlogpow : L ^ decay ≤ (2 : ℝ) ^ decay * Lm ^ decay := by
      have hLtwo : L ≤ 2 * Lm := by dsimp [L, Lm] at *; linarith
      calc
        L ^ decay ≤ (2 * Lm) ^ decay :=
          pow_le_pow_left₀ hLpos.le hLtwo decay
        _ = (2 : ℝ) ^ decay * Lm ^ decay := by rw [mul_pow]
    have hsourceScale : C * (M : ℝ) / Lm ^ decay ≤
        (C * (2 : ℝ) ^ decay) * (N : ℝ) / L ^ decay := by
      apply (div_le_div_iff₀ hLmPow hLpow).2
      have hMcoeff : C * (M : ℝ) ≤ C * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hMNreal hC.le
      calc
        (C * (M : ℝ)) * L ^ decay ≤
            (C * (N : ℝ)) * L ^ decay :=
          mul_le_mul_of_nonneg_right hMcoeff hLpow.le
        _ ≤ (C * (N : ℝ)) * ((2 : ℝ) ^ decay * Lm ^ decay) :=
          mul_le_mul_of_nonneg_left hlogpow (by positivity)
        _ = ((C * (2 : ℝ) ^ decay) * (N : ℝ)) * Lm ^ decay := by ring
    have htwo :
        ‖if 2 ≤ M then addChar (rationalCenter a q) (primeCubic 2) else (0 : ℂ)‖ ≤
          (1 : ℝ) := by
      split_ifs <;> simp
    have hodd : exerciseOddPrimeExpSum (rationalCenter a q) M =
        exerciseGeneralCubicPrimeSum a q 0 (-((a : ℝ) / q)) 0 M -
          (if 2 ≤ M then addChar (rationalCenter a q) (primeCubic 2) else 0) := by
      rw [exercise_generalCubicPrimeSum_eq_oddPrime_add_two]
      ring
    have htarget : C * (M : ℝ) / Lm ^ decay + 1 ≤
        (C * (2 : ℝ) ^ decay + 3) * (N : ℝ) / L ^ decay := by
      calc
        C * (M : ℝ) / Lm ^ decay + 1 ≤
            (C * (2 : ℝ) ^ decay) * (N : ℝ) / L ^ decay +
              (N : ℝ) / L ^ decay := add_le_add hsourceScale hNdivone
        _ = (C * (2 : ℝ) ^ decay + 1) * ((N : ℝ) / L ^ decay) := by ring
        _ ≤ (C * (2 : ℝ) ^ decay + 3) * ((N : ℝ) / L ^ decay) := by
          have hNdivnonneg : 0 ≤ (N : ℝ) / L ^ decay := by positivity
          exact mul_le_mul_of_nonneg_right (by norm_num) hNdivnonneg
        _ = (C * (2 : ℝ) ^ decay + 3) * (N : ℝ) / L ^ decay := by ring
    calc
      ‖exerciseOddPrimeExpSum (rationalCenter a q) M‖ =
          ‖exerciseGeneralCubicPrimeSum a q 0 (-((a : ℝ) / q)) 0 M -
            (if 2 ≤ M then addChar (rationalCenter a q) (primeCubic 2) else 0)‖ :=
        congrArg norm hodd
      _ ≤ ‖exerciseGeneralCubicPrimeSum a q 0 (-((a : ℝ) / q)) 0 M‖ +
          ‖if 2 ≤ M then addChar (rationalCenter a q) (primeCubic 2) else (0 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ C * (M : ℝ) / Lm ^ decay + 1 := by
        apply add_le_add _ htwo
        simpa only [Lm] using hprime
      _ ≤ (C * (2 : ℝ) ^ decay + 3) * (N : ℝ) / L ^ decay := htarget
      _ = (C * (2 : ℝ) ^ decay + 3) * (N : ℝ) /
          Real.log ((N : ℝ) + 2) ^ decay := by rfl

/-- **MIN-05, proved.** Bounded variation transfers rational-phase prefix
bounds to the actual frequency, costing only `1+8π`. No extra logarithm
is spent at this stage. -/
theorem exercise_wrapped_oddPrime_prefix_bound
    {alpha beta Delta : ℝ} {a q N : ℕ} {z : ℤ}
    (hDelta : 0 ≤ Delta)
    (happrox : alpha = rationalCenter a q + beta + z)
    (hscaled : (N : ℝ) ^ 3 * |beta| ≤ 1)
    (hprefix : ∀ M : ℕ, M ≤ N →
      ‖exerciseOddPrimeExpSum (rationalCenter a q) M‖ ≤ Delta) :
    ∀ M : ℕ, M ≤ N →
      ‖exerciseOddPrimeExpSum alpha M‖ ≤ Delta * (1 + 8 * Real.pi) := by
  classical
  intro M hMN
  by_cases hM : M = 0
  · subst M
    simp only [exerciseOddPrimeExpSum, Finset.Icc_self, Finset.sum_singleton]
    have hnot : ¬IsOddPrime 0 := fun h => Nat.not_prime_zero h.1
    simp only [hnot, if_false, norm_zero]
    positivity
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hscaledM : (M : ℝ) ^ 3 * |beta| ≤ 1 := by
      apply le_trans _ hscaled
      gcongr
    have hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) M,
        ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
          addChar (rationalCenter a q) (primeCubic k) *
            (if IsOddPrime k then (1 : ℂ) else 0)‖ ≤ Delta := by
      intro t ht
      have hfloor : ⌊t⌋₊ ≤ M := by
        exact (Nat.floor_le_floor ht.2).trans (by simp)
      simpa only [exerciseOddPrimeExpSum, mul_ite, mul_one, mul_zero] using
        hprefix ⌊t⌋₊ (hfloor.trans hMN)
    have hbound := norm_sum_addChar_wrapped_le_of_rationalPartialSums
      (fun k => if IsOddPrime k then (1 : ℂ) else 0)
      alpha beta a q z M hMpos hDelta hscaledM happrox hpartial
    simpa only [exerciseOddPrimeExpSum, mul_ite, mul_one, mul_zero] using hbound

private theorem exercise_sum_Icc_succ_eq_sum_Ioc
    (f : ℕ → ℂ) (M : ℕ) :
    (∑ k ∈ Finset.Icc 0 M, f (k + 1)) =
      ∑ p ∈ Finset.Ioc 0 (M + 1), f p := by
  classical
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_Ioc]
    omega
  · intro k hk j hj heq
    omega
  · intro p hp
    simp only [Finset.mem_Ioc] at hp
    refine ⟨p - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro k hk
    rfl

/-- **MIN-06, proved; elementary shifted Abel-summation exercise.**

The existing logarithm lemma uses `log(k+1)`; the prime weight is `log p`.
This precise shift must be proved, not hidden by a `simpa` that changes the
weight. For `N>0` use `c k := if IsOddPrime (k+1) then
addChar alpha (primeCubic (k+1)) else 0` on `0≤k≤N-1`.

1. Reindex `Icc 0 (N-1)` by `k↦k+1` to `Icc 1 N`; use
   `Finset.sum_bij` with inverse `p↦p-1` and `omega` for endpoints.
2. A prefix of this shifted sequence up to `floor t` is the original prime
   sum through `floor t+1`; its upper endpoint is ≤N. This supplies the
   premise of `norm_sum_log_mul_le_of_partialSumBound`.
3. Apply that lemma at `N-1`. Its endpoint logarithm is `log N`, bounded
   by `log(N+2)` via `Real.log_le_log`.
4. Rewrite prime von-Mangoldt coefficients with
   `ArithmeticFunction.vonMangoldt_apply_prime`. Translate the `Fin (N+1)`
   sum using `Fin.sum_univ_eq_sum_range` and `Nat.range_succ_eq_Icc_zero`.
5. Treat `N=1` separately by `simp [IsOddPrime]`; no odd prime occurs.

The result loses exactly one logarithm. -/
theorem exercise_log_weighted_oddPrime_bound
    {alpha Delta : ℝ} {N : ℕ} (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hprefix : ∀ M : ℕ, M ≤ N → ‖exerciseOddPrimeExpSum alpha M‖ ≤ Delta) :
    ‖cubicOddPrimeExpSum alpha N‖ ≤
      2 * Delta * Real.log ((N : ℝ) + 2) := by
  classical
  by_cases hN1 : N = 1
  · subst N
    have hzero : cubicOddPrimeExpSum alpha 1 = 0 := by
      unfold cubicOddPrimeExpSum
      rw [Fin.sum_univ_eq_sum_range
        (fun p : ℕ => if IsOddPrime p then
          (ArithmeticFunction.vonMangoldt p : ℂ) * addChar alpha (primeCubic p)
          else 0) 2]
      norm_num [IsOddPrime, Finset.sum_range_succ]
    rw [hzero, norm_zero]
    positivity
  have hN2 : 2 ≤ N := by omega
  have hNm : 0 < N - 1 := by omega
  let c : ℕ → ℂ := fun k =>
    if IsOddPrime (k + 1) then addChar alpha (primeCubic (k + 1)) else 0
  have hshifted (M : ℕ) :
      (∑ k ∈ Finset.Icc 0 M, c k) = exerciseOddPrimeExpSum alpha (M + 1) := by
    unfold exerciseOddPrimeExpSum
    rw [show (∑ k ∈ Finset.Icc 0 M, c k) =
        ∑ k ∈ Finset.Icc 0 M,
          (if IsOddPrime (k + 1) then
            addChar alpha (primeCubic (k + 1)) else 0) from rfl]
    rw [exercise_sum_Icc_succ_eq_sum_Ioc
      (fun p => if IsOddPrime p then addChar alpha (primeCubic p) else 0) M]
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 0 ≤ M + 1)]
    have hzero : ¬ IsOddPrime 0 := fun h => Nat.not_prime_zero h.1
    simp only [hzero, if_false, zero_add]
  have hpartial : ∀ M : ℕ, M ≤ N - 1 →
      ‖∑ k ∈ Finset.Icc 0 M, c k‖ ≤ Delta := by
    intro M hM
    rw [hshifted M]
    exact hprefix (M + 1) (by omega)
  have habel := CookMagyarCircle.norm_sum_log_mul_le_of_natPrefixBound
    c (N - 1) hNm hDelta hpartial
  have hweighted :
      (∑ k ∈ Finset.Icc 0 (N - 1),
        (Real.log ((k : ℝ) + 1) : ℂ) * c k) =
      ∑ p ∈ Finset.Ioc 0 N,
        (Real.log (p : ℝ) : ℂ) *
          (if IsOddPrime p then addChar alpha (primeCubic p) else 0) := by
    have hsub : N - 1 + 1 = N := by omega
    have hsum := exercise_sum_Icc_succ_eq_sum_Ioc
      (fun p => (Real.log (p : ℝ) : ℂ) *
        (if IsOddPrime p then addChar alpha (primeCubic p) else 0))
      (N - 1)
    rw [hsub] at hsum
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro k hk
    simp only [c, Nat.cast_add, Nat.cast_one]
  have hprime : cubicOddPrimeExpSum alpha N =
      ∑ p ∈ Finset.Ioc 0 N,
        (Real.log (p : ℝ) : ℂ) *
          (if IsOddPrime p then addChar alpha (primeCubic p) else 0) := by
    unfold cubicOddPrimeExpSum
    rw [Fin.sum_univ_eq_sum_range
      (fun p : ℕ => if IsOddPrime p then
        (ArithmeticFunction.vonMangoldt p : ℂ) * addChar alpha (primeCubic p)
        else 0) (N + 1)]
    rw [Nat.range_succ_eq_Icc_zero]
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 0 ≤ N)]
    have hzero : ¬ IsOddPrime 0 := fun h => Nat.not_prime_zero h.1
    simp only [hzero, if_false, zero_add]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hodd : IsOddPrime p
    · simp only [hodd, if_true]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hodd.1]
    · simp only [hodd, if_false, mul_zero]
  rw [hprime, ← hweighted]
  have hlog : Real.log ((N - 1 : ℕ) + 1 : ℝ) ≤
      Real.log ((N : ℝ) + 2) := by
    have hsub : N - 1 + 1 = N := by omega
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hsub
    rw [hcast]
    exact Real.log_le_log (by positivity) (by linarith)
  have hscale : 0 ≤ 2 * Delta := by positivity
  exact habel.trans (mul_le_mul_of_nonneg_left hlog hscale)

/-- **MIN-07, proved; elementary log-versus-power exercise.**
Start with `isBigO_cubicBadPrimePowerMass_sqrt`. After taking a fixed
constant `B`, it suffices eventually to show
`B*sqrt N*log(N+2)^saving≤N`. Apply
`isLittleO_log_rpow_rpow_atTop` with power `1/2`, composed with
`N↦(N:ℝ)+2`. Compare `sqrt(N+2)≤2*sqrt N` for `N≥1`, then use
`Real.sq_sqrt` and clear the positive `log(N+2)^saving` denominator.
Obtain the comparison before introducing `alpha`: this is a coefficient
mass estimate independent of the phase. -/
theorem exercise_eventually_bad_mass_log_saving (saving : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      cubicBadPrimePowerMass N ≤
        (N : ℝ) / Real.log ((N : ℝ) + 2) ^ saving := by
  obtain ⟨B, hB⟩ := (isBigO_iff.mp isBigO_cubicBadPrimePowerMass_sqrt)
  let D : ℝ := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlo : (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ saving) =o[atTop]
      (fun N : ℕ => ((N : ℝ) + 2) ^ (1 / 2 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ))
        (saving : ℝ) (by norm_num)).comp_tendsto harg
  filter_upwards [hB, hlo.bound (show 0 < (1 / (2 * D) : ℝ) by positivity),
    eventually_ge_atTop (1 : ℕ)] with N hmass hlog hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log ((N : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hLpow : 0 ≤ Real.log ((N : ℝ) + 2) ^ saving := by positivity
  have hroot : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt (N : ℝ)) ^ 2 = N :=
    Real.sq_sqrt (by positivity)
  have hrootShiftSq : (Real.sqrt ((N : ℝ) + 2)) ^ 2 = (N : ℝ) + 2 :=
    Real.sq_sqrt (by positivity)
  have hrootShift : Real.sqrt ((N : ℝ) + 2) ≤ 2 * Real.sqrt N := by
    have hrootShiftNonneg : 0 ≤ Real.sqrt ((N : ℝ) + 2) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 2) - 2 * Real.sqrt N)]
  have hlog' : Real.log ((N : ℝ) + 2) ^ saving ≤
      (1 / (2 * D)) * Real.sqrt ((N : ℝ) + 2) := by
    have hpowNonneg : 0 ≤ ((N : ℝ) + 2) ^ (1 / 2 : ℝ) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLpow,
      abs_of_nonneg hpowNonneg,
      one_mul, Real.sqrt_eq_rpow] using hlog
  have hDlog : D * Real.log ((N : ℝ) + 2) ^ saving ≤ Real.sqrt N := by
    have h := mul_le_mul_of_nonneg_left (hlog'.trans
      (mul_le_mul_of_nonneg_left hrootShift (by positivity))) hD.le
    have hDne : D ≠ 0 := ne_of_gt hD
    field_simp at h ⊢
    nlinarith
  have hmass' : cubicBadPrimePowerMass N ≤ D * Real.sqrt N := by
    have hB' : cubicBadPrimePowerMass N ≤ B * Real.sqrt N := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (cubicBadPrimePowerMass_nonneg N),
        abs_of_nonneg hroot] using hmass
    exact hB'.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [le_abs_self B]) hroot)
  apply (le_div_iff₀ (pow_pos hL _)).2
  calc
    cubicBadPrimePowerMass N * Real.log ((N : ℝ) + 2) ^ saving ≤
        (D * Real.sqrt N) * Real.log ((N : ℝ) + 2) ^ saving :=
      mul_le_mul_of_nonneg_right hmass' hLpow
    _ ≤ Real.sqrt N * Real.sqrt N := by
      nlinarith [mul_le_mul_of_nonneg_left hDlog hroot]
    _ = (N : ℝ) := by nlinarith [hrootSq]

/-- **MIN-08, proved assembly of exercises.** The source exponent is selected
once for the requested saving. All source dependencies are proved; this
wrapper adds no analytic hypothesis. -/
theorem exercise_prime_minor_arc_log_saving (saving : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ alpha ∈ minorArcs N
          (logarithmicDenominatorCutoff A N),
        ‖cubicVonMangoldtExpSum alpha N‖ ≤
          C * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ saving := by
  obtain ⟨E, hE, B, hB, hsource⟩ := exercise_rational_prime_log_saving (saving + 1)
  obtain ⟨K, hK, hprefixes⟩ := exercise_rational_prime_prefixes hE hB hsource
  let A := exerciseMinorCutoffExponent E (saving + 1)
  let C := 2 * K * (1 + 8 * Real.pi) + 1
  refine ⟨A, exerciseMinorCutoffExponent_pos _ _, C, by dsimp [C]; positivity, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 0 < Real.log ((N : ℝ) + 2) := by
    exact Eventually.of_forall fun N => Real.log_pos (by
      have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith)
  filter_upwards [hprefixes, exercise_eventually_bad_mass_log_saving saving,
    eventually_gt_atTop (0 : ℕ), hlog] with N hp hbad hN hL
  intro alpha hminor
  obtain ⟨a, q, beta, z, happrox, hscaled, hpartial⟩ := hp alpha hminor
  let Delta := K * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ (saving + 1)
  have hDelta : 0 ≤ Delta := by dsimp [Delta]; positivity
  have hwrapped := exercise_wrapped_oddPrime_prefix_bound
    hDelta happrox hscaled hpartial
  have hprime := exercise_log_weighted_oddPrime_bound hN
    (show 0 ≤ Delta * (1 + 8 * Real.pi) by positivity) hwrapped
  have hcancel :
      2 * (Delta * (1 + 8 * Real.pi)) * Real.log ((N : ℝ) + 2) =
        (2 * K * (1 + 8 * Real.pi)) * (N : ℝ) /
          Real.log ((N : ℝ) + 2) ^ saving := by
    dsimp [Delta]
    rw [pow_succ]
    field_simp
  calc
    ‖cubicVonMangoldtExpSum alpha N‖ ≤
        ‖cubicOddPrimeExpSum alpha N‖ + ‖cubicBadPrimePowerExpSum alpha N‖ := by
      rw [cubicVonMangoldtExpSum_eq_oddPrime_add_bad]
      exact norm_add_le _ _
    _ ≤ (2 * K * (1 + 8 * Real.pi)) * (N : ℝ) /
          Real.log ((N : ℝ) + 2) ^ saving +
        (N : ℝ) / Real.log ((N : ℝ) + 2) ^ saving := by
      exact add_le_add (hcancel ▸ hprime)
        ((norm_cubicBadPrimePowerExpSum_le_mass alpha N).trans hbad)
    _ = C * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ saving := by dsimp [C]; ring

/-- **MIN-09, proved elementary exponent bookkeeping.** At `n≥33`,
`34*(n-32)≥34`, so spending 32 weighted-moment logarithms leaves at least
two inverse logarithms. -/
theorem exercise_minor_log_envelope
    {n N : ℕ} (hn : 33 ≤ n) {C M L : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 1 ≤ L) :
    (C * (N : ℝ) / L ^ 34) ^ (n - 32) *
        (M * L ^ 32 * (N : ℝ) ^ 29) ≤
      (C ^ (n - 32) * M) * (N : ℝ) ^ (n - 3) / L ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have he : 1 ≤ n - 32 := by omega
  have hden : L ^ 34 ≤ L ^ (34 * (n - 32)) := by
    exact pow_le_pow_right₀ hL (by omega)
  have hpow : (C * (N : ℝ) / L ^ 34) ^ (n - 32) ≤
      (C ^ (n - 32) * (N : ℝ) ^ (n - 32)) / L ^ 34 := by
    rw [div_pow, mul_pow, ← pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hLpos _) hden
  have hNpow : (N : ℝ) ^ (n - 32) * (N : ℝ) ^ 29 = (N : ℝ) ^ (n - 3) := by
    rw [← pow_add]
    congr 1
    omega
  have hLpow : L ^ 32 / L ^ 34 = 1 / L ^ 2 := by
    have h34 : L ^ 34 = L ^ 32 * L ^ 2 := by ring
    rw [h34]
    field_simp
  calc
    _ ≤ (C ^ (n - 32) * (N : ℝ) ^ (n - 32) / L ^ 34) *
          (M * L ^ 32 * (N : ℝ) ^ 29) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (C ^ (n - 32) * M) *
          ((N : ℝ) ^ (n - 32) * (N : ℝ) ^ 29) * (L ^ 32 / L ^ 34) := by ring
    _ = (C ^ (n - 32) * M) * (N : ℝ) ^ (n - 3) / L ^ 2 := by
      rw [hNpow, hLpow]
      ring

/-- **MIN-10, proved constant absorption.** The eventual threshold can
depend on `K,c`; it has no target dependence. -/
theorem exercise_eventually_log_square_absorption
    {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      K / Real.log ((N : ℝ) + 2) ^ 2 ≤ c := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp harg
  filter_upwards [hlog.eventually_ge_atTop (Real.sqrt (K / c)),
    hlog.eventually_ge_atTop (1 : ℝ)] with N hroot hL
  simp only [Function.comp_def] at hroot hL
  have hLpos : 0 < Real.log ((N : ℝ) + 2) := by linarith
  apply (div_le_iff₀ (pow_pos hLpos 2)).2
  have hsq := Real.sq_sqrt (div_nonneg hK hc.le)
  have hroot_nonneg := Real.sqrt_nonneg (K / c)
  have hratio : K / c ≤ Real.log ((N : ℝ) + 2) ^ 2 := by nlinarith
  have hKbound := (div_le_iff₀ hc).mp hratio
  nlinarith

/-- **MIN-11, proved assembly of exercises; not an assumption-free theorem.**
This is the public consumer for `ExerciseGaps.lean`. Choose `A` once, before
choosing any arity or main-term coefficient. The remaining body uses the
already-proved weighted 32nd moment and deterministic minor-arc reduction;
all target dependence disappears because its character has norm one.
After the source exercises are filled, the same declaration becomes the
unconditional minor-error theorem without changing its statement. -/
theorem exercise_exists_minor_error_logarithmic_cutoff :
    ∃ A : ℕ, 0 < A ∧ ∀ n : ℕ, 33 ≤ n → ∀ c : ℝ, 0 < c →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
        ‖cubicMinorArcIntegral n N T (logarithmicDenominatorCutoff A N)‖ ≤
          c * cubicMainScale n N := by
  obtain ⟨A, hA, C, hC, hsup⟩ := exercise_prime_minor_arc_log_saving 34
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_integral_cubicVonMangoldtExpSum_pow32_le_auxiliary
  refine ⟨A, hA, ?_⟩
  intro n hn c hc
  let K := C ^ (n - 32) * M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp harg).eventually_ge_atTop (1 : ℝ)
  filter_upwards [hsup, hlog, exercise_eventually_log_square_absorption hK hc,
    eventually_ge_atTop (8 : ℕ)] with N hs hL hsmall hN
  simp only [Function.comp_def] at hL
  intro T
  have hbound := norm_cubicMinorArcIntegral_le_sup_pow_mul_thirtySecondMoment
    (T := T)
    (by omega : 32 ≤ n)
    (show 0 ≤ C * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ 34 by positivity) hs
  have hmomentN := hmoment N hN
  have hlog_mono : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 2) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hmomentL :
      (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) ≤
          M * Real.log ((N : ℝ) + 2) ^ 32 * (N : ℝ) ^ 29 := by
    apply hmomentN.trans
    gcongr
    exact log_succ_nonneg N
  calc
    ‖cubicMinorArcIntegral n N T (logarithmicDenominatorCutoff A N)‖ ≤
        (C * (N : ℝ) / Real.log ((N : ℝ) + 2) ^ 34) ^ (n - 32) *
          (M * Real.log ((N : ℝ) + 2) ^ 32 * (N : ℝ) ^ 29) :=
      hbound.trans (mul_le_mul_of_nonneg_left hmomentL (by positivity))
    _ ≤ K * (N : ℝ) ^ (n - 3) / Real.log ((N : ℝ) + 2) ^ 2 :=
      exercise_minor_log_envelope hn hC.le hM.le hL
    _ = (K / Real.log ((N : ℝ) + 2) ^ 2) * cubicMainScale n N := by
      unfold cubicMainScale
      ring
    _ ≤ c * cubicMainScale n N :=
      mul_le_mul_of_nonneg_right hsmall (by unfold cubicMainScale; positivity)

end SystolicGrowth.CookMagyarCircle

-- The source theorem and its final minor-arc consumers audit standard-only.
#print axioms SystolicGrowth.CookMagyarCircle.exercise_prime_minor_arc_log_saving
#print axioms SystolicGrowth.CookMagyarCircle.exercise_exists_minor_error_logarithmic_cutoff
-- These three bookkeeping lemmas should have only Lean's standard axioms.
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_of_mean_square
#print axioms SystolicGrowth.CookMagyarCircle.exercise_wrapped_oddPrime_prefix_bound
#print axioms SystolicGrowth.CookMagyarCircle.exercise_minor_log_envelope
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_log_square_absorption
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_bad_mass_log_saving
#print axioms SystolicGrowth.CookMagyarCircle.exercise_log_weighted_oddPrime_bound
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_large_endpoint_log_comparison
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_large_endpoint_denominator_window
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_mean_square_split
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_support_eq_stepNine_modOne
#print axioms SystolicGrowth.CookMagyarCircle.exercise_card_hua_typeII_inner_support_le
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_diagonal_le
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_offDiagonal_reindex
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_pair_window_iff
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_interval_swap
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_offDiagonal_eq_two_lowerOrdered
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_lowerOrdered_reindex
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_mean_square_eq_diagonal_add_ordered
#print axioms SystolicGrowth.CookMagyarCircle.exercise_hua_typeII_ordered_pair_window_iff
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_hua_source_dyadic_block_bound
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_hua_source_pair_bound_modOne
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_hua_pair_aggregate_harmonic_bound_modOne
#print axioms SystolicGrowth.CookMagyarCircle.exercise_rational_prime_prefixes
