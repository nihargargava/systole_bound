module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ClosedLoopPeriodicExtension
public import Geometry.PeriodicPathVariation
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Rebasing an actual closed loop

Periodic rebasing moves the basepoint without changing full variation or the
common Lipschitz bound. It supplies a unit-time wrapper across the closing join.
-/

open Set
open scoped Topology unitInterval NNReal

namespace SystolicGrowth

private theorem periodic_dist_le_of_unit_interval
    {M : Type*} [PseudoMetricSpace M] {K : ℝ≥0} {γ : ℝ → M}
    (hp : Function.Periodic γ 1)
    (hI : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) ≤ K * |u - v|) : LipschitzWith K γ := by
  have hshift (u : ℝ) (n : ℤ) : γ (u - n) = γ u := by
    simpa only [mul_one] using hp.sub_int_mul_eq (x := u) n
  have hfrac (u : ℝ) : γ (Int.fract u) = γ u := hshift u ⌊u⌋
  have hfi (u : ℝ) : Int.fract u ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hdiam (u v : ℝ) : dist (γ u) (γ v) ≤ K := by
    rw [← hfrac u, ← hfrac v]
    have h := hI _ (hfi u) _ (hfi v)
    have ha : |Int.fract u - Int.fract v| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hfi u).1, (hfi v).2], by linarith [(hfi u).2, (hfi v).1]⟩
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left ha K.coe_nonneg)
  have hordered (u v : ℝ) (huv : u ≤ v) : dist (γ u) (γ v) ≤ K * (v - u) := by
    by_cases hlong : 1 ≤ v - u
    · exact (hdiam u v).trans (by
        simpa using mul_le_mul_of_nonneg_left hlong K.coe_nonneg)
    · let U := u - (⌊u⌋ : ℝ)
      let V := v - (⌊u⌋ : ℝ)
      have hU : U ∈ Icc (0 : ℝ) 1 := hfi u
      have hUV : U ≤ V := by
        change u - (⌊u⌋ : ℝ) ≤ v - (⌊u⌋ : ℝ)
        linarith
      have hV0 : 0 ≤ V := hU.1.trans hUV
      have hV2 : V < 2 := by
        have hfract := Int.fract_lt_one u
        change u - (⌊u⌋ : ℝ) < 1 at hfract
        dsimp [V]
        linarith [not_le.mp hlong]
      rw [← hshift u ⌊u⌋, ← hshift v ⌊u⌋]
      change dist (γ U) (γ V) ≤ K * (v - u)
      by_cases hV1 : V ≤ 1
      · have h := hI U hU V ⟨hV0, hV1⟩
        rw [abs_of_nonpos (sub_nonpos.mpr hUV)] at h
        have he : -(U - V) = v - u := by
          change -(u - (⌊u⌋ : ℝ) - (v - (⌊u⌋ : ℝ))) = v - u
          ring
        rwa [he] at h
      · have hV' : V - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hleft := hI U hU 1 (by norm_num)
        have hright := hI 0 (by norm_num) (V - 1) hV'
        rw [abs_of_nonpos (by linarith [hU.2])] at hleft
        rw [zero_sub, abs_neg, abs_of_nonneg hV'.1] at hright
        have hVshift : γ (V - 1) = γ V := hp.sub_eq V
        have h01 : γ 1 = γ 0 := by simpa using hp 0
        calc
          dist (γ U) (γ V) ≤ dist (γ U) (γ 1) + dist (γ 1) (γ V) := dist_triangle _ _ _
          _ ≤ K * (-(U - 1)) + K * (V - 1) :=
            add_le_add hleft (by simpa only [h01, hVshift] using hright)
          _ = K * (v - u) := by
            change (K : ℝ) * (-(u - (⌊u⌋ : ℝ) - 1)) +
              (K : ℝ) * (v - (⌊u⌋ : ℝ) - 1) = (K : ℝ) * (v - u)
            ring
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq]
  rcases le_total u v with huv | hvu
  · simpa only [abs_of_nonpos (sub_nonpos.mpr huv), neg_sub] using hordered u v huv
  · simpa only [dist_comm, abs_of_nonneg (sub_nonneg.mpr hvu)] using hordered v u hvu

/-- A native Lipschitz closed loop retains the same global bound after
extension across every identified closing join. -/
theorem closedLoopPeriodicExtension_lipschitz
    {M : Type*} [PseudoMetricSpace M] {K : ℝ≥0}
    (f : closedLoopMapSet M) (hLip : LipschitzWith K f.1) :
    LipschitzWith K (closedLoopPeriodicExtension f) := by
  apply periodic_dist_le_of_unit_interval (closedLoopPeriodicExtension_periodic f)
  intro u hu v hv
  have h := hLip.dist_le_mul (⟨u, hu⟩ : unitInterval) (⟨v, hv⟩ : unitInterval)
  simpa only [← closedLoopPeriodicExtension_apply f, Subtype.dist_eq, Real.dist_eq] using h

/-- A genuine rotation of the closed loop, with its actual moved basepoint. -/
noncomputable def closedLoopRebase
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) (s : unitInterval) :
    closedLoopMapSet M :=
  ⟨⟨fun t => closedLoopPeriodicExtension f ((s : ℝ) + (t : ℝ)),
    (closedLoopPeriodicExtension_continuous f).comp (continuous_const.add continuous_subtype_val)⟩,
    by
      change closedLoopPeriodicExtension f ((s : ℝ) + 0) =
        closedLoopPeriodicExtension f ((s : ℝ) + 1)
      simpa only [add_zero] using (closedLoopPeriodicExtension_periodic f (s : ℝ)).symm⟩

@[simp] theorem closedLoopRebase_apply
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) (s t : unitInterval) :
    (closedLoopRebase f s).1 t = closedLoopPeriodicExtension f ((s : ℝ) + (t : ℝ)) := rfl

/-- Rotation preserves the common Lipschitz bound. -/
theorem closedLoopRebase_lipschitz
    {M : Type*} [PseudoMetricSpace M] {K : ℝ≥0}
    (f : closedLoopMapSet M) (s : unitInterval) (hLip : LipschitzWith K f.1) :
    LipschitzWith K (closedLoopRebase f s).1 := by
  have htranslation : LipschitzWith 1 (fun t : unitInterval => (s : ℝ) + (t : ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq, add_sub_add_left_eq_sub, Subtype.dist_eq, NNReal.coe_one, one_mul]
    exact le_rfl
  change LipschitzWith K (fun t : unitInterval => closedLoopPeriodicExtension f (s + (t : ℝ)))
  simpa only [mul_one, Function.comp_def] using
    (closedLoopPeriodicExtension_lipschitz f hLip).comp htranslation

/-- Rotation preserves exact full variation even when the variation is infinite. -/
theorem closedLoopRebase_eVariationOn
    {M : Type*} [PseudoEMetricSpace M] (f : closedLoopMapSet M) (s : unitInterval) :
    eVariationOn (closedLoopRebase f s).1 univ = eVariationOn f.1 univ := by
  have hcomp := eVariationOn.comp_eq_of_monotoneOn (closedLoopPeriodicExtension f)
    (t := univ) (fun t : unitInterval => (s : ℝ) + (t : ℝ))
    (fun u _ v _ h => by
      simpa only [add_comm] using add_le_add_left (show (u : ℝ) ≤ (v : ℝ) from h) (s : ℝ))
  have himage : (fun t : unitInterval => (s : ℝ) + (t : ℝ)) '' univ =
      Icc (s : ℝ) ((s : ℝ) + 1) := by
    ext u
    constructor
    · rintro ⟨t, _, rfl⟩
      constructor <;> linarith [t.property.1, t.property.2]
    · intro hu
      exact ⟨⟨u - s, by constructor <;> linarith [hu.1, hu.2]⟩, mem_univ _, by dsimp; ring⟩
  rw [himage] at hcomp
  have hperiod := eVariationOn_Icc_eq_of_periodic_of_mem_period
    (closedLoopPeriodicExtension f) zero_lt_one (closedLoopPeriodicExtension_periodic f)
    s.property.1 (by simpa only [zero_add] using s.property.2)
  simp only [zero_add] at hperiod
  change eVariationOn (fun t : unitInterval => closedLoopPeriodicExtension f (s + (t : ℝ))) univ = _
  simpa only [Function.comp_def] using hcomp.trans
    (hperiod.trans (closedLoopPeriodicExtension_eVariationOn f))

@[simp] theorem closedLoopRebase_zero
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) :
    closedLoopRebase f 0 = f := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  simpa only [closedLoopRebase_apply, Set.Icc.coe_zero, zero_add] using
    closedLoopPeriodicExtension_apply f t

/-- Rebasing preserves nullhomotopy despite its moved basepoint. The proof
constructs a homotopy of genuinely anchored loops, not a stability premise. -/
theorem closedLoopRebase_nullhomotopic_iff
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) (s : unitInterval) :
    (closedLoopPath (closedLoopRebase f s)).Homotopic
        (Path.refl ((closedLoopRebase f s).1 0)) ↔
      (closedLoopPath f).Homotopic (Path.refl (f.1 0)) := by
  let R : unitInterval → closedLoopMapSet M := fun u => closedLoopRebase f (s * u)
  let α : ∀ u : unitInterval, Path (f.1 0) ((R u).1 0) := fun u =>
    { toFun := fun t => closedLoopPeriodicExtension f ((s : ℝ) * (u : ℝ) * (t : ℝ))
      continuous_toFun := (closedLoopPeriodicExtension_continuous f).comp
        (continuous_const.mul continuous_subtype_val)
      source' := by simpa only [Set.Icc.coe_zero, mul_zero] using closedLoopPeriodicExtension_apply f 0
      target' := by simp only [R, closedLoopRebase_apply, Set.Icc.coe_mul,
        Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, add_zero] }
  have hα : Continuous ↿α := by
    change Continuous (fun p : unitInterval × unitInterval =>
      closedLoopPeriodicExtension f ((s : ℝ) * (p.1 : ℝ) * (p.2 : ℝ)))
    exact (closedLoopPeriodicExtension_continuous f).comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd))
  have hR : Continuous ↿fun u : unitInterval => closedLoopPath (R u) := by
    change Continuous (fun p : unitInterval × unitInterval =>
      closedLoopPeriodicExtension f ((s : ℝ) * (p.1 : ℝ) + (p.2 : ℝ)))
    exact (closedLoopPeriodicExtension_continuous f).comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).add
        (continuous_subtype_val.comp continuous_snd))
  let q : unitInterval → Path (f.1 0) (f.1 0) := fun u =>
    ((α u).trans (closedLoopPath (R u))).trans (α u).symm
  have hq : Continuous ↿q :=
    Path.trans_continuous_family
      (fun u => (α u).trans (closedLoopPath (R u)))
      (Path.trans_continuous_family α hα (fun u => closedLoopPath (R u)) hR)
      (fun u => (α u).symm) (Path.symm_continuous_family α hα)
  have hq01 : (q 0).Homotopic (q 1) := ⟨
    { toFun := fun p => q p.1 p.2
      continuous_toFun := hq
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl
      prop' := by
        intro u t ht
        rcases ht with rfl | rfl
        · change q u 0 = q 0 0
          rw [Path.source, Path.source]
        · change q u 1 = q 0 1
          rw [Path.target, Path.target] }⟩
  have hR0 : R 0 = f := by simp only [R, mul_zero, closedLoopRebase_zero]
  have hα0 (t : unitInterval) : α 0 t = f.1 0 := by
    change closedLoopPeriodicExtension f ((s : ℝ) * (0 : ℝ) * (t : ℝ)) = f.1 0
    simpa only [Set.Icc.coe_zero, mul_zero, zero_mul] using
      closedLoopPeriodicExtension_apply f 0
  have hloop0 (t : unitInterval) : closedLoopPath (R 0) t = closedLoopPath f t :=
    congrArg (fun g : closedLoopMapSet M => g.1 t) hR0
  have hq0 : (q 0).Homotopic (closedLoopPath f) := by
    have hq0eq : q 0 = ((Path.refl (f.1 0)).trans (closedLoopPath f)).trans
        (Path.refl (f.1 0)) := by
      apply Path.ext
      funext t
      simp only [q, Path.trans_apply, Path.symm_apply, Function.comp_apply,
        hα0, hloop0, Path.refl_apply]
    rw [hq0eq]
    exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _)
  have hR1 : R 1 = closedLoopRebase f s := by simp only [R, mul_one]
  have hconj : (q 1).Homotopic (Path.refl (f.1 0)) ↔
      (closedLoopPath (R 1)).Homotopic (Path.refl ((R 1).1 0)) := by
    constructor
    · exact Path.Homotopic.of_conj_nullhomotopic
    · intro h
      exact ((Path.Homotopic.trans_right_of_nullhomotopic h).hcomp
        (.refl (α 1).symm)).trans (Path.Homotopic.trans_symm (α 1))
  rw [← hR1]
  exact hconj.symm.trans ⟨fun h => hq0.symm.trans (hq01.trans h),
    fun h => hq01.symm.trans (hq0.trans h)⟩

end SystolicGrowth
