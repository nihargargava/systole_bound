module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIDifferencing
public import CookMagyar.HuaTypeIIInnerWindows
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# First Cauchy aggregation for Hua's Type-II ordered pairs

Hua's Lemma 6.3 (printed pp. 69--70) first fixes one member of an inner
pair, then applies Cauchy/differencing to the remaining variable-indexed
outer sums. The theorem below is the first exact finite stage: Cauchy in
the variable inner index and one positive outer-index difference. Every
shifted term keeps both members in the original three-interval common
window. It does not assert the later five-shift cancellation estimate.
-/

open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- For a fixed lower inner index `w`, Cauchy across the larger indices
`v` converts the sum of norms of the actual cubic ordered-pair sums into
their first positive-shift autocorrelations. The support is exactly
`D<u≤D'`, `P'/v<u≤(P/l)/v`, and `P'/w<u≤(P/l)/w` before and after the
shift; the original quadratic and linear coefficients remain in the
quadratic phase. This is the first finite constituent of Hua's repeated
Cauchy argument, not a Type-II saving. -/
theorem hua_typeII_fixedLowerPair_cauchy_firstDifference
    (P l D D' w a q : ℕ) (P' b c : ℝ) (V : Finset ℕ) :
    let W := V.filter (fun v => w < v)
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    (∑ v ∈ W, ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖) ^ 2 ≤
      (W.card : ℝ) *
        (∑ v ∈ W, (((U v).card : ℝ) +
          2 * (∑ h ∈ Finset.Icc 1 D',
            ∑ u ∈ (Finset.range (D' + 1 - h)).filter
              (fun u => u ∈ U v ∧ u + h ∈ U v),
                generalCubicPhase 0
                  (3 * A v * h)
                  (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
                  (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u).re)) := by
  dsimp only
  calc
    (∑ v ∈ V.filter (fun v => w < v),
        ‖∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
          generalCubicPhase
            (((a : ℝ) / q) * (l : ℝ) ^ 3 *
              ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
            (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
            (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u‖) ^ 2 ≤
      ((V.filter (fun v => w < v)).card : ℝ) *
        ∑ v ∈ V.filter (fun v => w < v),
          ‖∑ u ∈ huaTypeIICommonOuterWindow P l D D' v w P',
            generalCubicPhase
              (((a : ℝ) / q) * (l : ℝ) ^ 3 *
                ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
              (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
              (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = _ := by
      simp_rw [hua_typeII_ordered_pair_commonWindow_firstDifference]

#print axioms hua_typeII_fixedLowerPair_cauchy_firstDifference

/- TASK-SLOT HUA-TYPEII-HOLDER-EIGHTH (COMPLETE): M02 below. -/

/-- Eighth-power Hölder aggregation over the same fixed lower index and
exact common windows as the preceding first-difference theorem. This is
the finite cubic `k=3` aggregation in Hua's Lemma 6.3, not the ensuing
five-shift cancellation estimate. -/
theorem hua_typeII_fixedLowerPair_holder_eighth
    (P l D D' w a q : ℕ) (P' b c : ℝ) (V : Finset ℕ) :
    let W := V.filter (fun v => w < v)
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    (∑ v ∈ W, ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖) ^ 8 ≤
      (W.card : ℝ) ^ 7 *
        (∑ v ∈ W, ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8) := by
  dsimp only
  exact pow_sum_le_card_mul_sum_pow (fun _ _ => norm_nonneg _) 7

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_fixedLowerPair_holder_eighth

/- TASK-SLOT HUA-TYPEII-INTERVAL-ENVELOPE (COMPLETE): M03 below. -/

/-- If the available larger inner indices lie in `1..P₀`, the nonnegative
eighth-power side of Hölder can be enlarged to that whole interval. This
retains the exact common outer window for each `v` and fixed `w`; no
five-shift cancellation is asserted. -/
theorem hua_typeII_fixedLowerPair_holder_eighth_interval
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ) (V : Finset ℕ)
    (hV : V ⊆ Finset.Icc 1 P₀) :
    let W := V.filter (fun v => w < v)
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    (∑ v ∈ W, ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖) ^ 8 ≤
      (P₀ : ℝ) ^ 7 *
        (∑ v ∈ Finset.Icc 1 P₀,
          ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8) := by
  dsimp only
  let W := V.filter (fun v => w < v)
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
  let F := fun v : ℕ => ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8
  have hWsub : W ⊆ Finset.Icc 1 P₀ := (Finset.filter_subset _ _).trans hV
  have hcardNat : W.card ≤ P₀ := by
    calc
      W.card ≤ (Finset.Icc 1 P₀).card := Finset.card_le_card hWsub
      _ = P₀ := by simp [Nat.card_Icc]
  have hcard : (W.card : ℝ) ≤ (P₀ : ℝ) := by exact_mod_cast hcardNat
  have hsum : (∑ v ∈ W, F v) ≤ ∑ v ∈ Finset.Icc 1 P₀, F v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hWsub
    intro v _ _
    dsimp [F]
    positivity
  have hsum_nonneg : 0 ≤ ∑ v ∈ W, F v := Finset.sum_nonneg (by
    intro v _
    dsimp [F]
    positivity)
  calc
    (∑ v ∈ W, ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖) ^ 8 ≤
        (W.card : ℝ) ^ 7 * (∑ v ∈ W, F v) := by
          exact hua_typeII_fixedLowerPair_holder_eighth P l D D' w a q P' b c V
    _ ≤ (P₀ : ℝ) ^ 7 * (∑ v ∈ W, F v) := by
      apply mul_le_mul_of_nonneg_right ?_ hsum_nonneg
      gcongr
    _ ≤ (P₀ : ℝ) ^ 7 * (∑ v ∈ Finset.Icc 1 P₀, F v) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_fixedLowerPair_holder_eighth_interval

/- TASK-SLOT HUA-TYPEII-FIRST-OUTER-SHIFT (COMPLETE): exact finite eighth-power stage. -/

/-- First repeated-Cauchy constituent after interval enlargement. The eighth
power of each exact ordered-pair common-window sum is bounded by the diagonal
fourth power and fourth powers of its first positive-shift quadratic
correlations. The shifts lie in `1..D` under the source dyadic gate
`D' ≤ 2D`; all original endpoint tests and arbitrary lower coefficients
remain intact. This is not Hua's three-outer/two-inner shift estimate. -/
theorem hua_typeII_interval_eighth_firstOuterShift
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ)
    (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let T := fun v h : ℕ =>
      ∑ u ∈ (Finset.range (D' + 1 - h)).filter
          (fun u => u ∈ U v ∧ u + h ∈ U v),
        generalCubicPhase 0
          (3 * A v * h)
          (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
          (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u
    (∑ v ∈ Finset.Icc 1 P₀,
      ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8) ≤
      (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            ∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4)) := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
  let T := fun v h : ℕ =>
    ∑ u ∈ (Finset.range (D' + 1 - h)).filter
        (fun u => u ∈ U v ∧ u + h ∈ U v),
      generalCubicPhase 0
        (3 * A v * h)
        (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
        (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u
  have hTzero (v h : ℕ) (hh : D < h) : T v h = 0 := by
    dsimp [T]
    apply Finset.sum_eq_zero
    intro u hu
    obtain ⟨_, huU, huhU⟩ := Finset.mem_filter.mp hu
    obtain ⟨hDu, _, _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 huU
    obtain ⟨_, huhD', _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w (u + h) P').1 huhU
    omega
  have hTtruncate (v : ℕ) :
      (∑ h ∈ Finset.Icc 1 D', T v h) = ∑ h ∈ Finset.Icc 1 D, T v h := by
    symm
    apply Finset.sum_subset
    · intro h hh
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hh).1, (Finset.mem_Icc.mp hh).2.trans hDD'⟩
    · intro h hh hnot
      rw [hTzero v h (by
        have hh' := Finset.mem_Icc.mp hh
        have hnot' : ¬(1 ≤ h ∧ h ≤ D) := hnot ∘ Finset.mem_Icc.mpr
        omega)]
  have hpoint (v : ℕ) :
      ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8 ≤
        (((D + 1 : ℕ) : ℝ) ^ 3) *
          (((U v).card : ℝ) ^ 4 +
            16 * (∑ h ∈ Finset.Icc 1 D, ‖T v h‖ ^ 4)) := by
    let t : ℕ → ℝ := fun h => if h = 0 then ((U v).card : ℝ) else 2 * ‖T v h‖
    have ht (h : ℕ) (hh : h ∈ Finset.Icc 0 D) : 0 ≤ t h := by
      dsimp [t]
      split_ifs <;> positivity
    have hsep (f : ℕ → ℝ) :
        (∑ h ∈ Finset.Icc 0 D, f h) = f 0 + ∑ h ∈ Finset.Icc 1 D, f h := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le D)]
      simp
    have hsumt : (∑ h ∈ Finset.Icc 0 D, t h) =
        ((U v).card : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 D, ‖T v h‖ := by
      calc
        _ = t 0 + ∑ h ∈ Finset.Icc 1 D, t h := hsep t
        _ = ((U v).card : ℝ) +
            ∑ h ∈ Finset.Icc 1 D, 2 * ‖T v h‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro h hh
          simp [t, Nat.ne_of_gt (Finset.mem_Icc.mp hh).1]
        _ = _ := by rw [Finset.mul_sum]
    have hsumt4 : (∑ h ∈ Finset.Icc 0 D, t h ^ 4) =
        ((U v).card : ℝ) ^ 4 + 16 * ∑ h ∈ Finset.Icc 1 D, ‖T v h‖ ^ 4 := by
      calc
        _ = t 0 ^ 4 + ∑ h ∈ Finset.Icc 1 D, t h ^ 4 := hsep (fun h => t h ^ 4)
        _ = ((U v).card : ℝ) ^ 4 +
            ∑ h ∈ Finset.Icc 1 D, 16 * ‖T v h‖ ^ 4 := by
          congr 1
          apply Finset.sum_congr rfl
          intro h hh
          rw [show t h = 2 * ‖T v h‖ by
            simp [t, Nat.ne_of_gt (Finset.mem_Icc.mp hh).1]]
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hbase := hua_typeII_ordered_pair_commonWindow_firstDifference
      P l D D' v w a q P' b c
    change ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 2 =
      ((U v).card : ℝ) + 2 * (∑ h ∈ Finset.Icc 1 D', T v h).re at hbase
    have hre : (∑ h ∈ Finset.Icc 1 D', T v h).re ≤
        ∑ h ∈ Finset.Icc 1 D, ‖T v h‖ := by
      rw [hTtruncate v, Complex.re_sum]
      apply Finset.sum_le_sum
      intro h hh
      exact Complex.re_le_norm (T v h)
    have hboundSq :
        ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 2 ≤
          ∑ h ∈ Finset.Icc 0 D, t h := by
      calc
        _ = ((U v).card : ℝ) + 2 * (∑ h ∈ Finset.Icc 1 D', T v h).re := hbase
        _ ≤ ((U v).card : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 D, ‖T v h‖ := by
          linarith
        _ = _ := hsumt.symm
    have hpow :
        ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8 ≤
          (∑ h ∈ Finset.Icc 0 D, t h) ^ 4 := by
      calc
        _ = (‖∑ u ∈ U v,
          generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 2) ^ 4 := by ring
        _ ≤ _ := by gcongr
    have hholder : (∑ h ∈ Finset.Icc 0 D, t h) ^ 4 ≤
        (((D + 1 : ℕ) : ℝ) ^ 3) *
          (((U v).card : ℝ) ^ 4 +
            16 * (∑ h ∈ Finset.Icc 1 D, ‖T v h‖ ^ 4)) := by
      have h := pow_sum_le_card_mul_sum_pow ht 3
      simpa only [Nat.card_Icc, Nat.sub_zero, hsumt4] using h
    exact hpow.trans hholder
  calc
    (∑ v ∈ Finset.Icc 1 P₀,
      ‖∑ u ∈ U v, generalCubicPhase (A v) (B v) (C v) 0 u‖ ^ 8) ≤
        ∑ v ∈ Finset.Icc 1 P₀,
          (((D + 1 : ℕ) : ℝ) ^ 3) *
            (((U v).card : ℝ) ^ 4 +
              16 * (∑ h ∈ Finset.Icc 1 D, ‖T v h‖ ^ 4)) := by
                apply Finset.sum_le_sum
                intro v hv
                exact hpoint v
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm


#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_interval_eighth_firstOuterShift


/- TASK-SLOT HUA-TYPEII-SECOND-OUTER-SHIFT (COMPLETE): exact finite fourth-power stage. -/

/-- Quadratic-correlation fourth-power aggregation for one fixed positive
first shift. Second shifts beyond `D-h` have empty four-vertex support;
all original common-window tests and lower coefficients are retained. -/
theorem hua_typeII_interval_quadratic_fourth_secondOuterShift
    (P l D D' w a q P₀ h : ℕ) (P' b c : ℝ)
    (hDD' : D ≤ D') (hD' : D' ≤ 2 * D)
    (hh : h ∈ Finset.Icc 1 D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let W := fun v => (Finset.range (D' + 1 - h)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v)
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let T := fun v => ∑ u ∈ W v,
      generalCubicPhase 0
        (3 * A v * h)
        (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
        (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u
    let R := fun v k =>
      ∑ u ∈ (Finset.range ((D' - h) + 1 - k)).filter
          (fun u => u ∈ U v ∧ u + h ∈ U v ∧
            u + k ∈ U v ∧ u + k + h ∈ U v),
        generalCubicPhase 0 0
          (6 * A v * h * k)
          (3 * A v * h * (k : ℝ) ^ 2 +
            (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h) * k) u
    (∑ v ∈ Finset.Icc 1 P₀, ‖T v‖ ^ 4) ≤
      (((D - h + 1 : ℕ) : ℝ)) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((W v).card : ℝ) ^ 2) +
          4 * (∑ k ∈ Finset.Icc 1 (D - h),
            ∑ v ∈ Finset.Icc 1 P₀, ‖R v k‖ ^ 2)) := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let W := fun v => (Finset.range (D' + 1 - h)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v)
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
  let T := fun v => ∑ u ∈ W v,
    generalCubicPhase 0
      (3 * A v * h)
      (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
      (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u
  let R := fun v k =>
    ∑ u ∈ (Finset.range ((D' - h) + 1 - k)).filter
        (fun u => u ∈ U v ∧ u + h ∈ U v ∧
          u + k ∈ U v ∧ u + k + h ∈ U v),
      generalCubicPhase 0 0
        (6 * A v * h * k)
        (3 * A v * h * (k : ℝ) ^ 2 +
          (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h) * k) u
  have hhD : h ≤ D := (Finset.mem_Icc.mp hh).2
  have hhD' : h ≤ D' := hhD.trans hDD'
  have hRzero (v k : ℕ) (hk : D - h < k) : R v k = 0 := by
    dsimp [R]
    apply Finset.sum_eq_zero
    intro u hu
    obtain ⟨_, huU, _, _, hukhU⟩ := Finset.mem_filter.mp hu
    obtain ⟨hDu, _, _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 huU
    obtain ⟨_, hukhD', _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w (u + k + h) P').1 hukhU
    omega
  have hRtruncate (v : ℕ) :
      (∑ k ∈ Finset.Icc 1 (D' - h), R v k) =
        ∑ k ∈ Finset.Icc 1 (D - h), R v k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1,
          (Finset.mem_Icc.mp hk).2.trans (Nat.sub_le_sub_right hDD' h)⟩
    · intro k hk hnot
      rw [hRzero v k (by
        have hk' := Finset.mem_Icc.mp hk
        have hnot' : ¬(1 ≤ k ∧ k ≤ D - h) := hnot ∘ Finset.mem_Icc.mpr
        omega)]
  have hpoint (v : ℕ) :
      ‖T v‖ ^ 4 ≤ (((D - h + 1 : ℕ) : ℝ)) *
        (((W v).card : ℝ) ^ 2 +
          4 * (∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ ^ 2)) := by
    let t : ℕ → ℝ := fun k => if k = 0 then ((W v).card : ℝ) else 2 * ‖R v k‖
    have ht (k : ℕ) (hk : k ∈ Finset.Icc 0 (D - h)) : 0 ≤ t k := by
      dsimp [t]
      split_ifs <;> positivity
    have hsep (f : ℕ → ℝ) :
        (∑ k ∈ Finset.Icc 0 (D - h), f k) =
          f 0 + ∑ k ∈ Finset.Icc 1 (D - h), f k := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le (D - h))]
      simp
    have hsumt : (∑ k ∈ Finset.Icc 0 (D - h), t k) =
        ((W v).card : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ := by
      calc
        _ = t 0 + ∑ k ∈ Finset.Icc 1 (D - h), t k := hsep t
        _ = ((W v).card : ℝ) +
            ∑ k ∈ Finset.Icc 1 (D - h), 2 * ‖R v k‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          simp [t, Nat.ne_of_gt (Finset.mem_Icc.mp hk).1]
        _ = _ := by rw [Finset.mul_sum]
    have hsumt2 : (∑ k ∈ Finset.Icc 0 (D - h), t k ^ 2) =
        ((W v).card : ℝ) ^ 2 +
          4 * ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ ^ 2 := by
      calc
        _ = t 0 ^ 2 + ∑ k ∈ Finset.Icc 1 (D - h), t k ^ 2 :=
          hsep (fun k => t k ^ 2)
        _ = ((W v).card : ℝ) ^ 2 +
            ∑ k ∈ Finset.Icc 1 (D - h), 4 * ‖R v k‖ ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [show t k = 2 * ‖R v k‖ by
            simp [t, Nat.ne_of_gt (Finset.mem_Icc.mp hk).1]]
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hbase := hua_typeII_ordered_pair_commonWindow_secondDifference
      P l D D' v w a q h P' b c hhD'
    change ‖T v‖ ^ 2 =
      ((W v).card : ℝ) + 2 * (∑ k ∈ Finset.Icc 1 (D' - h), R v k).re at hbase
    have hre : (∑ k ∈ Finset.Icc 1 (D' - h), R v k).re ≤
        ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ := by
      rw [hRtruncate v, Complex.re_sum]
      apply Finset.sum_le_sum
      intro k hk
      exact Complex.re_le_norm (R v k)
    have hboundSq : ‖T v‖ ^ 2 ≤ ∑ k ∈ Finset.Icc 0 (D - h), t k := by
      calc
        _ = ((W v).card : ℝ) +
            2 * (∑ k ∈ Finset.Icc 1 (D' - h), R v k).re := hbase
        _ ≤ ((W v).card : ℝ) +
            2 * ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ := by linarith
        _ = _ := hsumt.symm
    have hpow : ‖T v‖ ^ 4 ≤ (∑ k ∈ Finset.Icc 0 (D - h), t k) ^ 2 := by
      calc
        _ = (‖T v‖ ^ 2) ^ 2 := by ring
        _ ≤ _ := by gcongr
    have hholder : (∑ k ∈ Finset.Icc 0 (D - h), t k) ^ 2 ≤
        (((D - h + 1 : ℕ) : ℝ)) *
          (((W v).card : ℝ) ^ 2 +
            4 * ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ ^ 2) := by
      have h := pow_sum_le_card_mul_sum_pow ht 1
      simpa only [Nat.card_Icc, Nat.sub_zero, hsumt2, pow_one] using h
    exact hpow.trans hholder
  calc
    (∑ v ∈ Finset.Icc 1 P₀, ‖T v‖ ^ 4) ≤
        ∑ v ∈ Finset.Icc 1 P₀,
          (((D - h + 1 : ℕ) : ℝ)) *
            (((W v).card : ℝ) ^ 2 +
              4 * ∑ k ∈ Finset.Icc 1 (D - h), ‖R v k‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro v hv
                exact hpoint v
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_interval_quadratic_fourth_secondOuterShift

/- TASK-SLOT HUA-TYPEII-THIRD-OUTER-SHIFT (COMPLETE): exact finite second moment. -/

/-- Aggregate the third outer difference over the whole inner interval before
taking a norm. The constant cubic third-difference phase retains all eight
original support tests, so its multiplicity may depend on `v`; no such
weight is discarded. -/
theorem hua_typeII_interval_linear_secondMoment_thirdOuterShift
    (P l D D' w a q P₀ h k : ℕ) (P' b : ℝ)
    (hDD' : D ≤ D') (hD' : D' ≤ 2 * D)
    (hh : h ∈ Finset.Icc 1 D)
    (hk : k ∈ Finset.Icc 1 (D - h)) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let X := fun v => (Finset.range ((D' - h) + 1 - k)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v ∧
        u + k ∈ U v ∧ u + k + h ∈ U v)
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let R := fun v => ∑ u ∈ X v,
      generalCubicPhase 0 0
        (6 * A v * h * k)
        (3 * A v * h * (k : ℝ) ^ 2 +
          (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h) * k) u
    let E := fun v r => (Finset.range ((D' - h - k) + 1 - r)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v ∧
        u + k ∈ U v ∧ u + k + h ∈ U v ∧
        u + r ∈ U v ∧ u + r + h ∈ U v ∧
        u + r + k ∈ U v ∧ u + r + k + h ∈ U v)
    let Z := fun v r => ∑ u ∈ E v r,
      generalCubicPhase 0 0 0 (6 * A v * h * k * r) u
    (∑ v ∈ Finset.Icc 1 P₀, ‖R v‖ ^ 2) ≤
      (∑ v ∈ Finset.Icc 1 P₀, ((X v).card : ℝ)) +
        2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
          ‖∑ v ∈ Finset.Icc 1 P₀, Z v r‖) := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let X := fun v => (Finset.range ((D' - h) + 1 - k)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v)
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let R := fun v => ∑ u ∈ X v,
    generalCubicPhase 0 0
      (6 * A v * h * k)
      (3 * A v * h * (k : ℝ) ^ 2 +
        (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h) * k) u
  let E := fun v r => (Finset.range ((D' - h - k) + 1 - r)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v ∧
      u + r ∈ U v ∧ u + r + h ∈ U v ∧
      u + r + k ∈ U v ∧ u + r + k + h ∈ U v)
  let Z := fun v r => ∑ u ∈ E v r,
    generalCubicPhase 0 0 0 (6 * A v * h * k * r) u
  have hhD : h ≤ D := (Finset.mem_Icc.mp hh).2
  have hhD' : h ≤ D' := hhD.trans hDD'
  have hkDh : k ≤ D - h := (Finset.mem_Icc.mp hk).2
  have hkD'h : k ≤ D' - h := hkDh.trans (Nat.sub_le_sub_right hDD' h)
  have hZzero (v r : ℕ) (hr : D - h - k < r) : Z v r = 0 := by
    dsimp [Z]
    apply Finset.sum_eq_zero
    intro u hu
    obtain ⟨_, huU, _, _, _, _, _, _, hurkhU⟩ := Finset.mem_filter.mp hu
    obtain ⟨hDu, _, _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 huU
    obtain ⟨_, hurkhD', _, _, _, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w
        (u + r + k + h) P').1 hurkhU
    omega
  have hZtruncate (v : ℕ) :
      (∑ r ∈ Finset.Icc 1 (D' - h - k), Z v r) =
        ∑ r ∈ Finset.Icc 1 (D - h - k), Z v r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr).1,
          (Finset.mem_Icc.mp hr).2.trans
            (Nat.sub_le_sub_right (Nat.sub_le_sub_right hDD' h) k)⟩
    · intro r hr hnot
      rw [hZzero v r (by
        have hr' := Finset.mem_Icc.mp hr
        have hnot' : ¬(1 ≤ r ∧ r ≤ D - h - k) :=
          hnot ∘ Finset.mem_Icc.mpr
        omega)]
  have hthird (v : ℕ) :
      ‖R v‖ ^ 2 = ((X v).card : ℝ) +
        2 * (∑ r ∈ Finset.Icc 1 (D - h - k), Z v r).re := by
    have hbase := hua_typeII_ordered_pair_commonWindow_thirdDifference
      P l D D' v w a q h k P' b hhD' hkD'h
    change ‖R v‖ ^ 2 = ((X v).card : ℝ) +
      2 * (∑ r ∈ Finset.Icc 1 (D' - h - k), Z v r).re at hbase
    rw [hZtruncate v] at hbase
    exact hbase
  have hrearr :
      (∑ v ∈ Finset.Icc 1 P₀,
        (∑ r ∈ Finset.Icc 1 (D - h - k), Z v r).re) =
      ∑ r ∈ Finset.Icc 1 (D - h - k),
        (∑ v ∈ Finset.Icc 1 P₀, Z v r).re := by
    simp only [Complex.re_sum]
    exact Finset.sum_comm
  have hrenorm :
      (∑ r ∈ Finset.Icc 1 (D - h - k),
        (∑ v ∈ Finset.Icc 1 P₀, Z v r).re) ≤
      ∑ r ∈ Finset.Icc 1 (D - h - k),
        ‖∑ v ∈ Finset.Icc 1 P₀, Z v r‖ := by
    apply Finset.sum_le_sum
    intro r hr
    exact Complex.re_le_norm _
  calc
    (∑ v ∈ Finset.Icc 1 P₀, ‖R v‖ ^ 2) =
        ∑ v ∈ Finset.Icc 1 P₀,
          (((X v).card : ℝ) +
            2 * (∑ r ∈ Finset.Icc 1 (D - h - k), Z v r).re) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact hthird v
    _ = (∑ v ∈ Finset.Icc 1 P₀, ((X v).card : ℝ)) +
        2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
          (∑ v ∈ Finset.Icc 1 P₀, Z v r).re) := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            rw [hrearr]
    _ ≤ _ := by linarith

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_interval_linear_secondMoment_thirdOuterShift


/- TASK-SLOT HUA-TYPEII-THREE-OUTER-AGGREGATE (COMPLETE): exact finite chain. -/

/-- Combining the three exact outer-difference stages bounds the full inner
interval eighth moment by diagonal terms and a signed cubic-phase sum for
each positive triple `h,k,r`. All eight original common-window tests remain
inside that final sum. This is the outer half of Hua's five-shift argument,
not the later inner differencing or source Type-II saving. -/
theorem hua_typeII_interval_eighth_threeOuterShift
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ)
    (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let W := fun v h => (Finset.range (D' + 1 - h)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v)
    let X := fun v h k => (Finset.range ((D' - h) + 1 - k)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v ∧
        u + k ∈ U v ∧ u + k + h ∈ U v)
    let E := fun v h k r => (Finset.range ((D' - h - k) + 1 - r)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v ∧
        u + k ∈ U v ∧ u + k + h ∈ U v ∧
        u + r ∈ U v ∧ u + r + h ∈ U v ∧
        u + r + k ∈ U v ∧ u + r + k + h ∈ U v)
    let S := fun v => ∑ u ∈ U v,
      generalCubicPhase (A v) (B v) (C v) 0 u
    let Z := fun v h k r => ∑ u ∈ E v h k r,
      generalCubicPhase 0 0 0 (6 * A v * h * k * r) u
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
      (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            (((D - h + 1 : ℕ) : ℝ)) *
              ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                4 * (∑ k ∈ Finset.Icc 1 (D - h),
                  ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                    2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                      ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)))))) := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
  let W := fun v h => (Finset.range (D' + 1 - h)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v)
  let X := fun v h k => (Finset.range ((D' - h) + 1 - k)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v)
  let E := fun v h k r => (Finset.range ((D' - h - k) + 1 - r)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v ∧
      u + r ∈ U v ∧ u + r + h ∈ U v ∧
      u + r + k ∈ U v ∧ u + r + k + h ∈ U v)
  let S := fun v => ∑ u ∈ U v,
    generalCubicPhase (A v) (B v) (C v) 0 u
  let T := fun v h => ∑ u ∈ W v h,
    generalCubicPhase 0
      (3 * A v * h)
      (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h)
      (A v * (h : ℝ) ^ 3 + B v * (h : ℝ) ^ 2 + C v * h) u
  let R := fun v h k => ∑ u ∈ X v h k,
    generalCubicPhase 0 0
      (6 * A v * h * k)
      (3 * A v * h * (k : ℝ) ^ 2 +
        (3 * A v * (h : ℝ) ^ 2 + 2 * B v * h) * k) u
  let Z := fun v h k r => ∑ u ∈ E v h k r,
    generalCubicPhase 0 0 0 (6 * A v * h * k * r) u
  have hfirst :
      (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
        (((D + 1 : ℕ) : ℝ) ^ 3) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
            16 * (∑ h ∈ Finset.Icc 1 D,
              ∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4)) := by
    exact hua_typeII_interval_eighth_firstOuterShift
      P l D D' w a q P₀ P' b c hDD' hD'
  have hsecond (h : ℕ) (hh : h ∈ Finset.Icc 1 D) :
      (∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4) ≤
        (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ∑ v ∈ Finset.Icc 1 P₀, ‖R v h k‖ ^ 2)) := by
    exact hua_typeII_interval_quadratic_fourth_secondOuterShift
      P l D D' w a q P₀ h P' b c hDD' hD' hh
  have hthird (h k : ℕ) (hh : h ∈ Finset.Icc 1 D)
      (hk : k ∈ Finset.Icc 1 (D - h)) :
      (∑ v ∈ Finset.Icc 1 P₀, ‖R v h k‖ ^ 2) ≤
        (∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
          2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
            ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖) := by
    exact hua_typeII_interval_linear_secondMoment_thirdOuterShift
      P l D D' w a q P₀ h k P' b hDD' hD' hh hk
  have hsecondFinal (h : ℕ) (hh : h ∈ Finset.Icc 1 D) :
      (∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4) ≤
        (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                  ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)))) := by
    calc
      _ ≤ (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ∑ v ∈ Finset.Icc 1 P₀, ‖R v h k‖ ^ 2)) := hsecond h hh
      _ ≤ _ := by
        have hsum :
            (∑ k ∈ Finset.Icc 1 (D - h),
              ∑ v ∈ Finset.Icc 1 P₀, ‖R v h k‖ ^ 2) ≤
            ∑ k ∈ Finset.Icc 1 (D - h),
              ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                  ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hthird h k hh hk
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
  calc
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
      (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            ∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4)) := hfirst
    _ ≤ _ := by
      have hsum :
          (∑ h ∈ Finset.Icc 1 D,
            ∑ v ∈ Finset.Icc 1 P₀, ‖T v h‖ ^ 4) ≤
          ∑ h ∈ Finset.Icc 1 D,
            (((D - h + 1 : ℕ) : ℝ)) *
              ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                4 * (∑ k ∈ Finset.Icc 1 (D - h),
                  ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                    2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                      ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)))) := by
        apply Finset.sum_le_sum
        intro h hh
        exact hsecondFinal h hh
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_interval_eighth_threeOuterShift


/-- The three outer-difference aggregate with its final signed sum exchanged
into the actual positive inner interval for each retained outer vertex.
The original eight outer support tests determine that interval exactly;
its existence as an `Icc` is proved in `HuaTypeIIInnerWindows`. No
variable outer multiplicity is removed from a signed sum. -/
theorem hua_typeII_interval_eighth_threeOuterShift_innerIntervals
    (P l D D' w a q P₀ : ℕ) (P' b c : ℝ)
    (hDD' : D ≤ D') (hD' : D' ≤ 2 * D) :
    let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
    let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    let W := fun v h => (Finset.range (D' + 1 - h)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v)
    let X := fun v h k => (Finset.range ((D' - h) + 1 - k)).filter
      (fun u => u ∈ U v ∧ u + h ∈ U v ∧
        u + k ∈ U v ∧ u + k + h ∈ U v)
    let S := fun v => ∑ u ∈ U v,
      generalCubicPhase (A v) (B v) (C v) 0 u
    let θ := fun h k r : ℕ =>
      6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r
    let H := fun h k r =>
      ∑ u ∈ Finset.range ((D' - h - k) + 1 - r),
        ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices
            P l D D' w P₀ P' {u, u + r + k + h},
          generalCubicPhase (θ h k r) 0 0
            (-(θ h k r) * (w : ℝ) ^ 3) v‖
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
      (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            (((D - h + 1 : ℕ) : ℝ)) *
              ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                4 * (∑ k ∈ Finset.Icc 1 (D - h),
                  ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                    2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r)))))) := by
  dsimp only
  let U := fun v => huaTypeIICommonOuterWindow P l D D' v w P'
  let A := fun v : ℕ => ((a : ℝ) / q) * (l : ℝ) ^ 3 *
    ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
  let B := fun v : ℕ => b * (l : ℝ) ^ 2 *
    ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
  let C := fun v : ℕ => c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
  let W := fun v h => (Finset.range (D' + 1 - h)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v)
  let X := fun v h k => (Finset.range ((D' - h) + 1 - k)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v)
  let E := fun v h k r => (Finset.range ((D' - h - k) + 1 - r)).filter
    (fun u => u ∈ U v ∧ u + h ∈ U v ∧
      u + k ∈ U v ∧ u + k + h ∈ U v ∧
      u + r ∈ U v ∧ u + r + h ∈ U v ∧
      u + r + k ∈ U v ∧ u + r + k + h ∈ U v)
  let S := fun v => ∑ u ∈ U v,
    generalCubicPhase (A v) (B v) (C v) 0 u
  let Z := fun v h k r => ∑ u ∈ E v h k r,
    generalCubicPhase 0 0 0 (6 * A v * h * k * r) u
  let θ := fun h k r : ℕ =>
    6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * h * k * r
  let H := fun h k r =>
    ∑ u ∈ Finset.range ((D' - h - k) + 1 - r),
      ‖∑ v ∈ huaTypeIIInnerWindowOnOuterVertices
          P l D D' w P₀ P' {u, u + r + k + h},
        generalCubicPhase (θ h k r) 0 0
          (-(θ h k r) * (w : ℝ) ^ 3) v‖
  have hbase :
      (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
        (((D + 1 : ℕ) : ℝ) ^ 3) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
            16 * (∑ h ∈ Finset.Icc 1 D,
              (((D - h + 1 : ℕ) : ℝ)) *
                ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                  4 * (∑ k ∈ Finset.Icc 1 (D - h),
                    ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                      2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                        ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)))))) := by
    exact hua_typeII_interval_eighth_threeOuterShift
      P l D D' w a q P₀ P' b c hDD' hD'
  have hterm (h k r : ℕ) :
      ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖ ≤ H h k r := by
    exact hua_typeII_threeOuter_sum_norm_le_innerWindow_norm_sum
      P l D D' w P₀ a q h k r P'
      (Finset.range ((D' - h - k) + 1 - r))
  have hsumr (h k : ℕ) :
      (∑ r ∈ Finset.Icc 1 (D - h - k),
        ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖) ≤
      ∑ r ∈ Finset.Icc 1 (D - h - k), H h k r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hterm h k r
  have hsumk (h : ℕ) :
      (∑ k ∈ Finset.Icc 1 (D - h),
        ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
          2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
            ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖))) ≤
      ∑ k ∈ Finset.Icc 1 (D - h),
        ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
          2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r)) := by
    apply Finset.sum_le_sum
    intro k hk
    have := hsumr h k
    linarith
  have hsumh :
      (∑ h ∈ Finset.Icc 1 D,
        (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                  ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖))))) ≤
      ∑ h ∈ Finset.Icc 1 D,
        (((D - h + 1 : ℕ) : ℝ)) *
          ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
            4 * (∑ k ∈ Finset.Icc 1 (D - h),
              ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                2 * (∑ r ∈ Finset.Icc 1 (D - h - k), H h k r)))) := by
    apply Finset.sum_le_sum
    intro h hh
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := hsumk h
    linarith
  calc
    (∑ v ∈ Finset.Icc 1 P₀, ‖S v‖ ^ 8) ≤
      (((D + 1 : ℕ) : ℝ) ^ 3) *
        ((∑ v ∈ Finset.Icc 1 P₀, ((U v).card : ℝ) ^ 4) +
          16 * (∑ h ∈ Finset.Icc 1 D,
            (((D - h + 1 : ℕ) : ℝ)) *
              ((∑ v ∈ Finset.Icc 1 P₀, ((W v h).card : ℝ) ^ 2) +
                4 * (∑ k ∈ Finset.Icc 1 (D - h),
                  ((∑ v ∈ Finset.Icc 1 P₀, ((X v h k).card : ℝ)) +
                    2 * (∑ r ∈ Finset.Icc 1 (D - h - k),
                      ‖∑ v ∈ Finset.Icc 1 P₀, Z v h k r‖)))))) := hbase
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith

#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_interval_eighth_threeOuterShift_innerIntervals

end SystolicGrowth.CookMagyarCircle
