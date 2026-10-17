module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricLoopCompactness
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Subpath
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Native path variation under restriction and concatenation

Monotone parameter changes identify the variation of each actual subpath.
Splitting at the concatenation join then adds the two original variations.
The identities apply to arbitrary paths, including infinite variation.
-/

open Set
open scoped unitInterval ENNReal

namespace SystolicGrowth

/-- A forward native subpath has exactly the variation of the original
path on its closed parameter interval. -/
theorem eVariationOn_path_subpath
    {M : Type*} [PseudoEMetricSpace M] {x y : M} (p : Path x y)
    {a b : unitInterval} (hab : a ≤ b) :
    eVariationOn (p.subpath a b) univ = eVariationOn p (Icc a b) := by
  have hmono : Monotone (Set.Icc.convexComb a b) := by
    intro s t hst
    change (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) ≤
      (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)
    have hab' : (a : ℝ) ≤ (b : ℝ) := hab
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]
  change eVariationOn (p ∘ Set.Icc.convexComb a b) univ = eVariationOn p (Icc a b)
  rw [eVariationOn.comp_eq_of_monotoneOn p _ (hmono.monotoneOn univ), image_univ,
    Path.range_subpathAux, uIcc_of_le hab]

/-- Native concatenation adds the two full variations, without a finite
variation premise or cancellation of extended-real values. -/
theorem eVariationOn_path_trans
    {M : Type*} [PseudoEMetricSpace M] {x y z : M}
    (p : Path x y) (q : Path y z) :
    eVariationOn (p.trans q) univ = eVariationOn p univ + eVariationOn q univ := by
  let c : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hc0 : (0 : unitInterval) ≤ c := c.2.1
  have hc1 : c ≤ (1 : unitInterval) := c.2.2
  have hleftFun : ((p.trans q).subpath 0 c : unitInterval → M) = p := by
    funext t
    change (p.trans q) (Set.Icc.convexComb 0 c t) = p t
    have hcoord : (Set.Icc.convexComb 0 c t : ℝ) = (t : ℝ) / 2 := by
      simp only [Set.Icc.coe_convexComb, Set.Icc.coe_zero, c]
      ring
    have hhalf : (Set.Icc.convexComb 0 c t : ℝ) ≤ 1 / 2 := by
      rw [hcoord]
      linarith [t.2.2]
    rw [← Path.extend_apply _ (Set.Icc.convexComb 0 c t).2,
      Path.extend_trans_of_le_half p q hhalf, hcoord]
    have hparam : 2 * ((t : ℝ) / 2) = (t : ℝ) := by ring
    rw [hparam, p.extend_apply t.2]
  have hrightFun : ((p.trans q).subpath c 1 : unitInterval → M) = q := by
    funext t
    change (p.trans q) (Set.Icc.convexComb c 1 t) = q t
    have hcoord : (Set.Icc.convexComb c 1 t : ℝ) = (1 + (t : ℝ)) / 2 := by
      simp only [Set.Icc.coe_convexComb, Set.Icc.coe_one, c]
      ring
    have hhalf : 1 / 2 ≤ (Set.Icc.convexComb c 1 t : ℝ) := by
      rw [hcoord]
      linarith [t.2.1]
    rw [← Path.extend_apply _ (Set.Icc.convexComb c 1 t).2,
      Path.extend_trans_of_half_le p q hhalf, hcoord]
    have hparam : 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ) := by ring
    rw [hparam, q.extend_apply t.2]
  have hleft : eVariationOn (p.trans q) (Icc 0 c) = eVariationOn p univ := by
    rw [← eVariationOn_path_subpath (p.trans q) hc0]
    rw [hleftFun]
  have hright : eVariationOn (p.trans q) (Icc c 1) = eVariationOn q univ := by
    rw [← eVariationOn_path_subpath (p.trans q) hc1]
    rw [hrightFun]
  have hsplit := eVariationOn.Icc_add_Icc (s := univ) (p.trans q)
    hc0 hc1 (mem_univ c)
  simpa only [univ_inter, ← unitInterval.univ_eq_Icc, hleft, hright] using hsplit.symm

/-- A genuine unit-time constant-speed metric segment has variation exactly
equal to its native endpoint distance. -/
theorem eVariationOn_path_eq_of_metric_segment
    {M : Type*} [MetricSpace M] {x y : M} (p : Path x y)
    (hsegment : ∀ s t : unitInterval,
      dist (p s) (p t) = dist x y * |s.val - t.val|) :
    eVariationOn p univ = ENNReal.ofReal (dist x y) := by
  have hlip : LipschitzWith (nndist x y) p := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hsegment s t]
    simp only [coe_nndist, Subtype.dist_eq, Real.dist_eq]
    exact le_rfl
  apply le_antisymm
  · simpa only [← edist_nndist, edist_dist, Path.coe_toContinuousMap] using
      eVariationOn_unitInterval_le_of_lipschitz p.toContinuousMap hlip
  · have hbound := eVariationOn.edist_le p (mem_univ (0 : unitInterval))
      (mem_univ (1 : unitInterval))
    simpa only [p.source, p.target, edist_dist] using hbound

#print axioms eVariationOn_path_subpath
#print axioms eVariationOn_path_trans
#print axioms eVariationOn_path_eq_of_metric_segment

end SystolicGrowth
