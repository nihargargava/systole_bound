module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Subpath
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite Lipschitz bounds for actual path operations

Native affine subpaths do not increase a unit-time Lipschitz constant.
Concatenation has an explicit finite speed bound, including across its join.
The bound need not be sharp: arclength normalization subsequently restores
the shortened curve's actual total-length speed.
-/

open Set
open scoped unitInterval NNReal

namespace SystolicGrowth

/-- Arbitrary forward or reversed native subpaths retain the original
Lipschitz bound on the unit interval. -/
theorem lipschitzWith_path_subpath
    {M : Type*} [PseudoMetricSpace M] {x y : M} (p : Path x y) {K : ℝ≥0}
    (hp : LipschitzWith K p) (a b : unitInterval) :
    LipschitzWith K (p.subpath a b) := by
  have hcomb : LipschitzWith 1 (Set.Icc.convexComb a b) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change |((1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ)) -
      ((1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ))| ≤
        1 * |(s : ℝ) - (t : ℝ)|
    have hfactor : ((1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ)) -
        ((1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)) =
          ((b : ℝ) - (a : ℝ)) * ((s : ℝ) - (t : ℝ)) := by ring
    rw [hfactor, abs_mul]
    have hab : |(b : ℝ) - (a : ℝ)| ≤ 1 := abs_le.mpr (by
      constructor <;> linarith [a.2.1, a.2.2, b.2.1, b.2.2])
    exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)
  change LipschitzWith K (p ∘ Set.Icc.convexComb a b)
  simpa only [mul_one] using hp.comp hcomb

/-- Native concatenation retains a finite explicit Lipschitz bound across
the actual joining endpoint, not only separately on its two halves. -/
theorem lipschitzWith_path_trans
    {M : Type*} [PseudoMetricSpace M] {x y z : M}
    (p : Path x y) (q : Path y z) {K L : ℝ≥0}
    (hp : LipschitzWith K p) (hq : LipschitzWith L q) :
    LipschitzWith (2 * (K + L)) (p.trans q) := by
  have hpExtend : LipschitzWith K p.extend := by
    simpa only [mul_one, Path.extend, ContinuousMap.coe_mk, IccExtend] using
      hp.comp (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))
  have hqExtend : LipschitzWith L q.extend := by
    simpa only [mul_one, Path.extend, ContinuousMap.coe_mk, IccExtend] using
      hq.comp (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))
  have hordered (s t : unitInterval) (hst : s ≤ t) :
      dist ((p.trans q) s) ((p.trans q) t) ≤
        (2 * ((K : ℝ) + (L : ℝ))) * dist s t := by
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    rw [← Path.extend_extends' (p.trans q) s, ← Path.extend_extends' (p.trans q) t]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have hs : (s : ℝ) ≤ 1 / 2 := hst'.trans ht
      rw [Path.extend_trans_of_le_half p q hs, Path.extend_trans_of_le_half p q ht]
      have hbound := hpExtend.dist_le_mul (2 * (s : ℝ)) (2 * (t : ℝ))
      have hparam : dist (2 * (s : ℝ)) (2 * (t : ℝ)) = 2 * dist s t := by
        simp only [Real.dist_eq, Subtype.dist_eq, ← mul_sub, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hparam] at hbound
      nlinarith [mul_nonneg L.coe_nonneg (dist_nonneg : 0 ≤ dist s t)]
    · have ht' : 1 / 2 ≤ (t : ℝ) := (not_le.mp ht).le
      by_cases hs : 1 / 2 ≤ (s : ℝ)
      · rw [Path.extend_trans_of_half_le p q hs, Path.extend_trans_of_half_le p q ht']
        have hbound := hqExtend.dist_le_mul (2 * (s : ℝ) - 1) (2 * (t : ℝ) - 1)
        have hparam : dist (2 * (s : ℝ) - 1) (2 * (t : ℝ) - 1) = 2 * dist s t := by
          have hdiff : (2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1) =
              2 * ((s : ℝ) - (t : ℝ)) := by ring
          simp only [Real.dist_eq, Subtype.dist_eq, hdiff, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [hparam] at hbound
        nlinarith [mul_nonneg K.coe_nonneg (dist_nonneg : 0 ≤ dist s t)]
      · have hs' : (s : ℝ) ≤ 1 / 2 := (not_le.mp hs).le
        rw [Path.extend_trans_of_le_half p q hs', Path.extend_trans_of_half_le p q ht']
        have hleft := hpExtend.dist_le_mul (2 * (s : ℝ)) 1
        have hright := hqExtend.dist_le_mul 0 (2 * (t : ℝ) - 1)
        rw [p.extend_one, Real.dist_eq, abs_of_nonpos (by linarith : 2 * (s : ℝ) - 1 ≤ 0)]
          at hleft
        rw [q.extend_zero, Real.dist_eq,
          abs_of_nonpos (by linarith : 0 - (2 * (t : ℝ) - 1) ≤ 0)] at hright
        have htriangle := dist_triangle (p.extend (2 * (s : ℝ))) y
          (q.extend (2 * (t : ℝ) - 1))
        have hdist : dist s t = (t : ℝ) - (s : ℝ) := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst')]
          ring
        rw [hdist]
        nlinarith [mul_nonneg L.coe_nonneg (by linarith : 0 ≤ 1 - 2 * (s : ℝ)),
          mul_nonneg K.coe_nonneg (by linarith : 0 ≤ 2 * (t : ℝ) - 1)]
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist ((p.trans q) s) ((p.trans q) t) ≤
    (2 * ((K : ℝ) + (L : ℝ))) * dist s t
  rcases le_total s t with hst | hts
  · exact hordered s t hst
  · simpa only [dist_comm] using hordered t s hts

#print axioms lipschitzWith_path_subpath
#print axioms lipschitzWith_path_trans

end SystolicGrowth
