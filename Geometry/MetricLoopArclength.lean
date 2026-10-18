module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricLoopCompactness
public import Geometry.GluingLoopNullhomotopyOpenness
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.LeftRight

@[expose] public section

/-!
# Arclength coordinates for metric loops

The cumulative metric variation supplies a continuous monotone coordinate
for every continuous finite-variation curve. Its increments bound all chords,
including on constant-coordinate plateaus. The original Lipschitz APIs are
retained as corollaries of this rectifiable-curve construction.
-/

open Set
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth

/-- Cumulative variation along a unit-time curve, as a real coordinate. -/
noncomputable def metricVariationCoordinate {M : Type*} [MetricSpace M]
    (f : C(unitInterval, M)) (t : unitInterval) : ℝ :=
  (eVariationOn f (Icc 0 t)).toReal

private theorem boundedVariationOn_unitInterval_of_lipschitz
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) : BoundedVariationOn f univ :=
  ne_top_of_le_ne_top (by simp) (eVariationOn_unitInterval_le_of_lipschitz f hf)

/-- The variation on a subinterval is bounded by its duration times the
original Lipschitz constant. -/
theorem eVariationOn_unitInterval_Icc_le_of_lipschitz
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) (s t : unitInterval) :
    eVariationOn f (Icc s t) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ((t : ℝ) - s) := by
  have hmono : MonotoneOn (fun u : unitInterval => (u : ℝ)) univ :=
    fun _ _ _ _ h => h
  have hid : eVariationOn (id : unitInterval → unitInterval) (Icc s t) ≤
      ENNReal.ofReal ((t : ℝ) - s) := by
    change eVariationOn (fun u : unitInterval => (u : ℝ)) (Icc s t) ≤ _
    simpa only [univ_inter] using
      hmono.eVariationOn_le (a := s) (b := t) (mem_univ _) (mem_univ _)
  have hbound := hf.lipschitzOnWith.comp_eVariationOn_le
    (g := id) (s := Icc s t) (mapsTo_univ id (Icc s t))
  change eVariationOn f (Icc s t) ≤
    (K : ℝ≥0∞) * eVariationOn (id : unitInterval → unitInterval) (Icc s t) at hbound
  exact hbound.trans (mul_le_mul_right hid _)

/-- Cumulative variation increments are the exact subinterval variations. -/
theorem metricVariationCoordinate_sub_eq_of_boundedVariation
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M))
    (hfin : BoundedVariationOn f univ) {s t : unitInterval} (hst : s ≤ t) :
    metricVariationCoordinate f t - metricVariationCoordinate f s =
      (eVariationOn f (Icc s t)).toReal := by
  have hadd : eVariationOn f (Icc 0 s) + eVariationOn f (Icc s t) =
      eVariationOn f (Icc 0 t) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc f (s := univ) (unitInterval.nonneg s) hst (mem_univ s)
  have hreal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (hfin.mono (subset_univ _))
    (hfin.mono (subset_univ _))] at hreal
  dsimp only [metricVariationCoordinate]
  linarith

/-- The Lipschitz version of the exact cumulative variation increment. -/
theorem metricVariationCoordinate_sub_eq
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) {s t : unitInterval} (hst : s ≤ t) :
    metricVariationCoordinate f t - metricVariationCoordinate f s =
      (eVariationOn f (Icc s t)).toReal :=
  metricVariationCoordinate_sub_eq_of_boundedVariation f
    (boundedVariationOn_unitInterval_of_lipschitz f hf) hst

/-- The cumulative variation coordinate is monotone. -/
theorem metricVariationCoordinate_monotone_of_boundedVariation
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M))
    (hfin : BoundedVariationOn f univ) : Monotone (metricVariationCoordinate f) := by
  intro s t hst
  have hinc := metricVariationCoordinate_sub_eq_of_boundedVariation f hfin hst
  have hnonneg := ENNReal.toReal_nonneg (a := eVariationOn f (Icc s t))
  linarith

/-- A Lipschitz curve's cumulative variation is monotone. -/
theorem metricVariationCoordinate_monotone
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) : Monotone (metricVariationCoordinate f) :=
  metricVariationCoordinate_monotone_of_boundedVariation f
    (boundedVariationOn_unitInterval_of_lipschitz f hf)

/-- Every chord is bounded by the difference of arclength coordinates;
in particular, equal coordinates force equal curve values. -/
theorem dist_le_metricVariationCoordinate_sub_of_boundedVariation
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M))
    (hfin : BoundedVariationOn f univ) (s t : unitInterval) :
    dist (f s) (f t) ≤ |metricVariationCoordinate f s - metricVariationCoordinate f t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
    (metricVariationCoordinate_monotone_of_boundedVariation f hfin hst)),
    metricVariationCoordinate_sub_eq_of_boundedVariation f hfin hst]
  exact (hfin.mono (subset_univ _)).dist_le (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)

/-- The chord bound for a Lipschitz curve, including variation plateaus. -/
theorem dist_le_metricVariationCoordinate_sub
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) (s t : unitInterval) :
    dist (f s) (f t) ≤ |metricVariationCoordinate f s - metricVariationCoordinate f t| :=
  dist_le_metricVariationCoordinate_sub_of_boundedVariation f
    (boundedVariationOn_unitInterval_of_lipschitz f hf) s t

/-- The original speed bound makes cumulative variation Lipschitz, hence
continuous; no strict monotonicity or absence of plateaus is needed. -/
theorem metricVariationCoordinate_lipschitz
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (metricVariationCoordinate f) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hfin := boundedVariationOn_unitInterval_of_lipschitz f hf
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s t]
    exact this t s (le_of_not_ge hst)
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
    (metricVariationCoordinate_monotone f hf hst)), metricVariationCoordinate_sub_eq f hf hst]
  have hbound := eVariationOn_unitInterval_Icc_le_of_lipschitz f hf s t
  have hreal := (ENNReal.toReal_le_toReal (hfin.mono (subset_univ _))
    (by finiteness)).mpr hbound
  have hstreal : (s : ℝ) ≤ t := hst
  change (eVariationOn f (Icc s t)).toReal ≤ (K : ℝ) * |(s : ℝ) - t|
  rw [abs_of_nonpos (sub_nonpos.mpr hstreal), neg_sub]
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hstreal)] using hreal

@[simp] theorem metricVariationCoordinate_zero
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) :
    metricVariationCoordinate f 0 = 0 := by
  simp [metricVariationCoordinate]

@[simp] theorem metricVariationCoordinate_one
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) :
    metricVariationCoordinate f 1 = (eVariationOn f univ).toReal := by
  rw [metricVariationCoordinate, ← unitInterval.univ_eq_Icc]

/-- Continuity of a finite-variation curve removes both one-sided jumps
of its cumulative variation, including at unit-interval endpoints. -/
theorem metricVariationCoordinate_continuous_of_boundedVariation
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M))
    (hfin : BoundedVariationOn f univ) : Continuous (metricVariationCoordinate f) := by
  have hVeq : metricVariationCoordinate f = variationOnFromTo f univ 0 := by
    funext t
    rw [variationOnFromTo.eq_of_le f univ (show (0 : unitInterval) ≤ t from t.property.1)]
    simp only [metricVariationCoordinate, univ_inter]
  rw [hVeq]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · simpa only [ContinuousWithinAt, univ_inter, dist_self, sub_zero] using
      variationOnFromTo.tendsto_left (mem_univ (0 : unitInterval)) (mem_univ t)
        hfin.locallyBoundedVariationOn
        (f.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  · simpa only [ContinuousWithinAt, univ_inter, dist_self, add_zero] using
      variationOnFromTo.tendsto_right (mem_univ (0 : unitInterval)) (mem_univ t)
        hfin.locallyBoundedVariationOn
        (f.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- A positive-length continuous rectifiable curve factors through a monotone surjective
arclength reparameterization. The new Lipschitz constant is its actual
length. Plateaus are collapsed by the proved
chord bound. -/
theorem exists_rectifiable_arclength_factorization
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M))
    (hfin : BoundedVariationOn f univ) (hl : 0 < (eVariationOn f univ).toReal) :
    ∃ a : C(unitInterval, M), ∃ ρ : C(unitInterval, unitInterval),
      LipschitzWith ⟨(eVariationOn f univ).toReal, ENNReal.toReal_nonneg⟩ a ∧
      Monotone ρ ∧ ρ 0 = 0 ∧ ρ 1 = 1 ∧ Function.Surjective ρ ∧
      (∀ t, f t = a (ρ t)) ∧ eVariationOn a univ = eVariationOn f univ := by
  classical
  let l := (eVariationOn f univ).toReal
  let V := metricVariationCoordinate f
  have hV : Continuous V := metricVariationCoordinate_continuous_of_boundedVariation f hfin
  have hVmono : Monotone V := metricVariationCoordinate_monotone_of_boundedVariation f hfin
  have hV0 : V 0 = 0 := metricVariationCoordinate_zero f
  have hV1 : V 1 = l := metricVariationCoordinate_one f
  have hVbounds (t : unitInterval) : 0 ≤ V t ∧ V t ≤ l := by
    constructor
    · simpa only [hV0] using hVmono (show (0 : unitInterval) ≤ t from t.property.1)
    · simpa only [hV1] using hVmono (show t ≤ (1 : unitInterval) from t.property.2)
  let ρ : C(unitInterval, unitInterval) :=
    ⟨fun t => ⟨V t / l, div_nonneg (hVbounds t).1 hl.le,
      (div_le_one hl).mpr (hVbounds t).2⟩,
      (hV.div_const l).subtype_mk _⟩
  have hρmono : Monotone ρ := by
    intro s t hst
    exact div_le_div_of_nonneg_right (hVmono hst) hl.le
  have hρ0 : ρ 0 = 0 := by
    apply Subtype.ext
    change V 0 / l = 0
    rw [hV0, zero_div]
  have hρ1 : ρ 1 = 1 := by
    apply Subtype.ext
    change V 1 / l = 1
    rw [hV1, div_self hl.ne']
  have hρsurj : Function.Surjective ρ := by
    intro t
    have hrange : Icc (0 : ℝ) 1 ⊆ range (fun s => (ρ s : ℝ)) := by
      simpa only [Function.comp_apply, hρ0, hρ1, Set.Icc.coe_zero, Set.Icc.coe_one] using
        intermediate_value_univ (0 : unitInterval) 1
          (f := fun s => (ρ s : ℝ))
          (continuous_subtype_val.comp ρ.continuous)
    obtain ⟨s, hs⟩ := hrange t.property
    exact ⟨s, Subtype.ext hs⟩
  obtain ⟨q, hq⟩ := hρsurj.hasRightInverse
  have hVq (t : unitInterval) : V (q t) = l * (t : ℝ) := by
    have h := congrArg (fun t : unitInterval => (t : ℝ)) (hq t)
    change V (q t) / l = (t : ℝ) at h
    exact ((div_eq_iff hl.ne').mp h).trans (mul_comm _ _)
  let A : unitInterval → M := fun t => f (q t)
  have hAlip : LipschitzWith ⟨l, hl.le⟩ A := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hchord := dist_le_metricVariationCoordinate_sub_of_boundedVariation f hfin (q s) (q t)
    change dist (A s) (A t) ≤ |V (q s) - V (q t)| at hchord
    rw [hVq s, hVq t, ← mul_sub, abs_mul, abs_of_nonneg hl.le] at hchord
    exact hchord
  let a : C(unitInterval, M) := ⟨A, hAlip.continuous⟩
  have hfactor (t : unitInterval) : f t = a (ρ t) := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hchord := dist_le_metricVariationCoordinate_sub_of_boundedVariation f hfin t (q (ρ t))
    change dist (f t) (a (ρ t)) ≤ |V t - V (q (ρ t))| at hchord
    rw [hVq, show l * (ρ t : ℝ) = V t by
      change l * (V t / l) = V t
      exact mul_div_cancel₀ _ hl.ne', sub_self, abs_zero] at hchord
    exact hchord
  have hvariation : eVariationOn a univ = eVariationOn f univ := by
    have hcomp : (f : unitInterval → M) = a ∘ ρ := funext hfactor
    rw [hcomp, eVariationOn.comp_eq_of_monotoneOn a ρ
      (fun _ _ _ _ h => hρmono h)]
    rw [image_univ, hρsurj.range_eq]
  exact ⟨a, ρ, hAlip, hρmono, hρ0, hρ1, hρsurj, hfactor, hvariation⟩

/-- A Lipschitz curve admits the same actual-length arclength factorization. -/
theorem exists_lipschitz_arclength_factorization
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hl : 0 < (eVariationOn f univ).toReal) :
    ∃ a : C(unitInterval, M), ∃ ρ : C(unitInterval, unitInterval),
      LipschitzWith ⟨(eVariationOn f univ).toReal, ENNReal.toReal_nonneg⟩ a ∧
      Monotone ρ ∧ ρ 0 = 0 ∧ ρ 1 = 1 ∧ Function.Surjective ρ ∧
      (∀ t, f t = a (ρ t)) ∧ eVariationOn a univ = eVariationOn f univ :=
  exists_rectifiable_arclength_factorization f
    (boundedVariationOn_unitInterval_of_lipschitz f hf) hl

/-- Arclength normalization preserves a closed loop's actual basepoint,
variation, and based homotopy class. The endpoint cast records the proved
basepoint equality rather than assuming it. -/
theorem exists_rectifiable_arclength_closedLoop
    {M : Type*} [MetricSpace M] (f : closedLoopMapSet M)
    (hfin : BoundedVariationOn f.1 univ) (hl : 0 < (eVariationOn f.1 univ).toReal) :
    ∃ a : closedLoopMapSet M, ∃ hbase : f.1 0 = a.1 0,
      LipschitzWith ⟨(eVariationOn f.1 univ).toReal, ENNReal.toReal_nonneg⟩ a.1 ∧
      eVariationOn a.1 univ = eVariationOn f.1 univ ∧
      (closedLoopPath f).Homotopic ((closedLoopPath a).cast hbase hbase) := by
  obtain ⟨a, ρ, hLip, _, hρ0, hρ1, _, hfactor, hvariation⟩ :=
    exists_rectifiable_arclength_factorization f.1 hfin hl
  have hbase : f.1 0 = a 0 := by simpa only [hρ0] using hfactor 0
  have hclosed : a 0 = a 1 := by
    calc
      a 0 = f.1 0 := hbase.symm
      _ = f.1 1 := f.2
      _ = a 1 := by simpa only [hρ1] using hfactor 1
  let A : closedLoopMapSet M := ⟨a, hclosed⟩
  let p : Path (f.1 0) (f.1 0) := (closedLoopPath A).cast hbase hbase
  have hpath : p.reparam ρ ρ.continuous hρ0 hρ1 = closedLoopPath f := by
    apply Path.ext
    funext t
    exact (hfactor t).symm
  have hhomotopic : p.Homotopic (closedLoopPath f) := by
    rw [← hpath]
    exact ⟨Path.Homotopy.reparam p ρ ρ.continuous hρ0 hρ1⟩
  exact ⟨A, hbase, hLip, hvariation, hhomotopic.symm⟩

/-- The original Lipschitz closed-loop normalization API, as a corollary
of the continuous rectifiable-loop constructor. -/
theorem exists_lipschitz_arclength_closedLoop
    {M : Type*} [MetricSpace M] (f : closedLoopMapSet M) {K : ℝ≥0}
    (hf : LipschitzWith K f.1) (hl : 0 < (eVariationOn f.1 univ).toReal) :
    ∃ a : closedLoopMapSet M, ∃ hbase : f.1 0 = a.1 0,
      LipschitzWith ⟨(eVariationOn f.1 univ).toReal, ENNReal.toReal_nonneg⟩ a.1 ∧
      eVariationOn a.1 univ = eVariationOn f.1 univ ∧
      (closedLoopPath f).Homotopic ((closedLoopPath a).cast hbase hbase) :=
  exists_rectifiable_arclength_closedLoop f
    (boundedVariationOn_unitInterval_of_lipschitz f.1 hf) hl

end SystolicGrowth
