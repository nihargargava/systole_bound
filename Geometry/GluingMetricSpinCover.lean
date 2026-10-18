module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeTangentQuotientIdentification
public import Geometry.GluingUnitTangentMetricChange
public import Geometry.GluingSpinChainCovering
public import Geometry.GluingSpinCircleAction

@[expose] public section

/-!
# Actual spin double covers of native and replacement unit tangent bundles

The constructed retained-frame quotient is identified with the real native
unit tangent bundle. Positive radial normalization then transports its spin
covering to any actual continuous positive metric on the same tangent bundle.
No replacement metric or global lift is postulated, and no conformality or
rotation-equivariance is asserted for an anisotropic metric change.
-/

open Set Bundle
open scoped Manifold Topology unitInterval

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The genuine global spin square, taking values in the literal native
unit tangent total space through the constructed frame identification. -/
def gluedNativeUnitSpinSquare (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedSpinCarrier → P.NativeUnitTangentCarrier :=
  P.gluedTangentNativeUnitHomeomorph ∘ P.gluedSpinSquare

/-- Native spin transport preserves the actual underlying glued basepoint. -/
@[simp] theorem gluedNativeUnitSpinSquare_proj
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    (P.gluedNativeUnitSpinSquare q).val.proj = P.gluedSpinBase q := by
  rw [gluedNativeUnitSpinSquare, Function.comp_apply,
    P.gluedTangentNativeUnitHomeomorph_proj, P.gluedTangentBase_gluedSpinSquare]

/-- The actual two-sheet spin square is continuous in the genuine native
tangent total-space topology. -/
theorem gluedNativeUnitSpinSquare_continuous
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.gluedNativeUnitSpinSquare :=
  P.gluedTangentNativeUnitHomeomorph.continuous.comp P.continuous_gluedSpinSquare

/-- Every actual native unit tangent has a spin over it. -/
theorem gluedNativeUnitSpinSquare_surjective
    (P : ExerciseGluingPreparation C g n genera X) :
    Function.Surjective P.gluedNativeUnitSpinSquare :=
  P.gluedTangentNativeUnitHomeomorph.surjective.comp P.gluedSpinSquare_surjective

/-- Native spin transport is a genuine covering map, not only a pointwise
two-to-one map. -/
theorem gluedNativeUnitSpinSquare_isCoveringMap
    (P : ExerciseGluingPreparation C g n genera X) :
    IsCoveringMap P.gluedNativeUnitSpinSquare :=
  P.gluedSpinSquare_isCoveringMap.homeomorph_comp P.gluedTangentNativeUnitHomeomorph

/-- Identification with the actual native unit bundle adds no spin fibers. -/
theorem gluedNativeUnitSpinSquare_eq_iff
    (P : ExerciseGluingPreparation C g n genera X) (q r : P.GluedSpinCarrier) :
    P.gluedNativeUnitSpinSquare q = P.gluedNativeUnitSpinSquare r ↔
      q = r ∨ q = P.gluedSpinAntipode r := by
  change P.gluedTangentNativeUnitHomeomorph (P.gluedSpinSquare q) =
    P.gluedTangentNativeUnitHomeomorph (P.gluedSpinSquare r) ↔ _
  rw [P.gluedTangentNativeUnitHomeomorph.injective.eq_iff]
  exact P.gluedSpinSquare_eq_iff q r

/-- The literal central spin involution remains in the actual native cover's
fiber; it does not negate the underlying unit tangent. -/
@[simp] theorem gluedNativeUnitSpinSquare_antipode
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedNativeUnitSpinSquare (P.gluedSpinAntipode q) =
      P.gluedNativeUnitSpinSquare q := by
  exact congrArg P.gluedTangentNativeUnitHomeomorph
    (P.gluedSpinSquare_gluedSpinAntipode q)

/-- Every actual native spin fiber is the exact pair of a spin and its
distinct literal spin antipode. -/
theorem gluedNativeUnitSpinSquare_fiber
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedNativeUnitSpinSquare ⁻¹' {P.gluedNativeUnitSpinSquare q} =
      {q, P.gluedSpinAntipode q} := by
  ext r
  exact P.gluedNativeUnitSpinSquare_eq_iff r q

/-- Both actual native spin sheets exist and exhaust the fiber. -/
theorem gluedNativeUnitSpinSquare_two_distinct
    (P : ExerciseGluingPreparation C g n genera X) (v : P.NativeUnitTangentCarrier) :
    ∃ q : P.GluedSpinCarrier,
      P.gluedNativeUnitSpinSquare ⁻¹' {v} = {q, P.gluedSpinAntipode q} ∧
        q ≠ P.gluedSpinAntipode q := by
  obtain ⟨q, rfl⟩ := P.gluedNativeUnitSpinSquare_surjective v
  exact ⟨q, P.gluedNativeUnitSpinSquare_fiber q, (P.gluedSpinAntipode_ne q).symm⟩

/-- A native spin fiber has exactly two actual points. -/
theorem gluedNativeUnitSpinSquare_fiber_ncard
    (P : ExerciseGluingPreparation C g n genera X) (v : P.NativeUnitTangentCarrier) :
    (P.gluedNativeUnitSpinSquare ⁻¹' {v}).ncard = 2 := by
  obtain ⟨q, hq, hne⟩ := P.gluedNativeUnitSpinSquare_two_distinct v
  rw [hq]
  exact Set.ncard_pair hne

/-- The existing genuine frame-fiber turn, transported into the literal
native unit tangent bundle by its proved global identification. -/
def gluedNativeUnitFiberTurn (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedTangentCarrier) :
    Path (P.gluedTangentNativeUnitHomeomorph q) (P.gluedTangentNativeUnitHomeomorph q) :=
  (P.tangentFiberTurn q).map P.gluedTangentNativeUnitHomeomorph.continuous

@[simp] theorem gluedNativeUnitFiberTurn_proj
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) (t : I) :
    (P.gluedNativeUnitFiberTurn q t).val.proj = P.gluedTangentBase q := by
  change (P.gluedTangentNativeUnitHomeomorph
    (Circle.exp (2 * Real.pi * (t : ℝ)) • q)).val.proj = _
  rw [P.gluedTangentNativeUnitHomeomorph_proj, P.gluedTangentBase_circle_smul]

/-- The real native covering lifts this actual unit-fiber loop to the
constructed spin half-turn; no monodromy witness is assumed. -/
theorem liftPath_gluedNativeUnitFiberTurn
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedNativeUnitSpinSquare_isCoveringMap.liftPath
      (P.gluedNativeUnitFiberTurn (P.gluedSpinSquare q)) q
      (P.gluedNativeUnitFiberTurn (P.gluedSpinSquare q)).source =
        (P.spinFiberTurn q : C(I, P.GluedSpinCarrier)) := by
  symm
  apply (P.gluedNativeUnitSpinSquare_isCoveringMap.eq_liftPath_iff'
    (P.gluedNativeUnitFiberTurn (P.gluedSpinSquare q)).source).mpr
  refine ⟨?_, (P.spinFiberTurn q).source⟩
  funext t
  exact congrArg P.gluedTangentNativeUnitHomeomorph (P.gluedSpinSquare_spinFiberTurn q t)

theorem liftPath_gluedNativeUnitFiberTurn_one_ne
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedNativeUnitSpinSquare_isCoveringMap.liftPath
      (P.gluedNativeUnitFiberTurn (P.gluedSpinSquare q)) q
      (P.gluedNativeUnitFiberTurn (P.gluedSpinSquare q)).source 1 ≠ q := by
  rw [P.liftPath_gluedNativeUnitFiberTurn]
  change P.spinFiberTurn q 1 ≠ q
  rw [(P.spinFiberTurn q).target]
  exact P.gluedSpinAntipode_ne q

variable (P : ExerciseGluingPreparation C g n genera X)
  (m : ContinuousRiemannianMetric ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))

/-- The real retained-frame carrier is transported to an actual metric's
unit tangent bundle by positive radial normalization, preserving its base. -/
def gluedTangentMetricUnitHomeomorph :
    P.GluedTangentCarrier ≃ₜ P.MetricUnitTangentCarrier m :=
  P.gluedTangentNativeUnitHomeomorph.trans (P.nativeUnitTangentMetricHomeomorph m)

@[simp] theorem gluedTangentMetricUnitHomeomorph_proj (q : P.GluedTangentCarrier) :
    (P.gluedTangentMetricUnitHomeomorph m q).val.proj = P.gluedTangentBase q := by
  change (P.unitTangentMetricChange P.gluedContinuousRiemannianMetric m
    (P.gluedTangentNativeUnitHomeomorph q)).val.proj = _
  rw [P.unitTangentMetricChange_proj, P.gluedTangentNativeUnitHomeomorph_proj]

/-- The genuine global spin covering of the unit tangent bundle of the
supplied actual continuous positive metric. -/
def gluedMetricUnitSpinSquare : P.GluedSpinCarrier → P.MetricUnitTangentCarrier m :=
  P.gluedTangentMetricUnitHomeomorph m ∘ P.gluedSpinSquare

/-- This is literal metric transport of the constructed native spin cover. -/
@[simp] theorem gluedMetricUnitSpinSquare_eq_native (q : P.GluedSpinCarrier) :
    P.gluedMetricUnitSpinSquare m q =
      P.nativeUnitTangentMetricHomeomorph m (P.gluedNativeUnitSpinSquare q) := rfl

@[simp] theorem gluedMetricUnitSpinSquare_proj (q : P.GluedSpinCarrier) :
    (P.gluedMetricUnitSpinSquare m q).val.proj = P.gluedSpinBase q := by
  rw [gluedMetricUnitSpinSquare, Function.comp_apply,
    P.gluedTangentMetricUnitHomeomorph_proj, P.gluedTangentBase_gluedSpinSquare]

theorem gluedMetricUnitSpinSquare_continuous : Continuous (P.gluedMetricUnitSpinSquare m) :=
  (P.gluedTangentMetricUnitHomeomorph m).continuous.comp P.continuous_gluedSpinSquare

theorem gluedMetricUnitSpinSquare_surjective :
    Function.Surjective (P.gluedMetricUnitSpinSquare m) :=
  (P.gluedTangentMetricUnitHomeomorph m).surjective.comp P.gluedSpinSquare_surjective

/-- The real global spin covering survives every positive continuous metric
change on the actual tangent bundle. -/
theorem gluedMetricUnitSpinSquare_isCoveringMap :
    IsCoveringMap (P.gluedMetricUnitSpinSquare m) :=
  P.gluedSpinSquare_isCoveringMap.homeomorph_comp (P.gluedTangentMetricUnitHomeomorph m)

/-- Metric change neither collapses nor adds any actual spin sheets. -/
theorem gluedMetricUnitSpinSquare_eq_iff (q r : P.GluedSpinCarrier) :
    P.gluedMetricUnitSpinSquare m q = P.gluedMetricUnitSpinSquare m r ↔
      q = r ∨ q = P.gluedSpinAntipode r := by
  change P.gluedTangentMetricUnitHomeomorph m (P.gluedSpinSquare q) =
    P.gluedTangentMetricUnitHomeomorph m (P.gluedSpinSquare r) ↔ _
  rw [(P.gluedTangentMetricUnitHomeomorph m).injective.eq_iff]
  exact P.gluedSpinSquare_eq_iff q r

@[simp] theorem gluedMetricUnitSpinSquare_antipode (q : P.GluedSpinCarrier) :
    P.gluedMetricUnitSpinSquare m (P.gluedSpinAntipode q) =
      P.gluedMetricUnitSpinSquare m q := by
  exact congrArg (P.gluedTangentMetricUnitHomeomorph m)
    (P.gluedSpinSquare_gluedSpinAntipode q)

theorem gluedMetricUnitSpinSquare_fiber (q : P.GluedSpinCarrier) :
    P.gluedMetricUnitSpinSquare m ⁻¹' {P.gluedMetricUnitSpinSquare m q} =
      {q, P.gluedSpinAntipode q} := by
  ext r
  exact P.gluedMetricUnitSpinSquare_eq_iff m r q

/-- Every actual replacement unit tangent has precisely the two distinct
spins constructed before replacement, without a metric-specific spin axiom. -/
theorem gluedMetricUnitSpinSquare_two_distinct (v : P.MetricUnitTangentCarrier m) :
    ∃ q : P.GluedSpinCarrier,
      P.gluedMetricUnitSpinSquare m ⁻¹' {v} = {q, P.gluedSpinAntipode q} ∧
        q ≠ P.gluedSpinAntipode q := by
  obtain ⟨q, rfl⟩ := P.gluedMetricUnitSpinSquare_surjective m v
  exact ⟨q, P.gluedMetricUnitSpinSquare_fiber m q, (P.gluedSpinAntipode_ne q).symm⟩

theorem gluedMetricUnitSpinSquare_fiber_ncard (v : P.MetricUnitTangentCarrier m) :
    (P.gluedMetricUnitSpinSquare m ⁻¹' {v}).ncard = 2 := by
  obtain ⟨q, hq, hne⟩ := P.gluedMetricUnitSpinSquare_two_distinct m v
  rw [hq]
  exact Set.ncard_pair hne

/-- The real frame-fiber turn transported to the supplied metric's actual
unit tangent bundle. This is not an arbitrary-metric rotation formula. -/
def gluedMetricUnitFiberTurn (q : P.GluedTangentCarrier) :
    Path (P.gluedTangentMetricUnitHomeomorph m q) (P.gluedTangentMetricUnitHomeomorph m q) :=
  (P.tangentFiberTurn q).map (P.gluedTangentMetricUnitHomeomorph m).continuous

@[simp] theorem gluedMetricUnitFiberTurn_proj (q : P.GluedTangentCarrier) (t : I) :
    (P.gluedMetricUnitFiberTurn m q t).val.proj = P.gluedTangentBase q := by
  change (P.gluedTangentMetricUnitHomeomorph m
    (Circle.exp (2 * Real.pi * (t : ℝ)) • q)).val.proj = _
  rw [P.gluedTangentMetricUnitHomeomorph_proj, P.gluedTangentBase_circle_smul]

/-- Actual metric change preserves the explicitly lifted spin half-turn
and its endpoint, with no rotation-equivariance premise. -/
theorem liftPath_gluedMetricUnitFiberTurn (q : P.GluedSpinCarrier) :
    (P.gluedMetricUnitSpinSquare_isCoveringMap m).liftPath
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)) q
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).source =
        (P.spinFiberTurn q : C(I, P.GluedSpinCarrier)) := by
  symm
  apply ((P.gluedMetricUnitSpinSquare_isCoveringMap m).eq_liftPath_iff'
    (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).source).mpr
  refine ⟨?_, (P.spinFiberTurn q).source⟩
  funext t
  exact congrArg (P.gluedTangentMetricUnitHomeomorph m) (P.gluedSpinSquare_spinFiberTurn q t)

theorem liftPath_gluedMetricUnitFiberTurn_one_ne (q : P.GluedSpinCarrier) :
    (P.gluedMetricUnitSpinSquare_isCoveringMap m).liftPath
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)) q
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).source 1 ≠ q := by
  rw [P.liftPath_gluedMetricUnitFiberTurn]
  change P.spinFiberTurn q 1 ≠ q
  rw [(P.spinFiberTurn q).target]
  exact P.gluedSpinAntipode_ne q

#print axioms gluedNativeUnitSpinSquare_proj
#print axioms gluedNativeUnitSpinSquare_isCoveringMap
#print axioms gluedNativeUnitSpinSquare_two_distinct
#print axioms liftPath_gluedNativeUnitFiberTurn_one_ne
#print axioms gluedTangentMetricUnitHomeomorph
#print axioms gluedMetricUnitSpinSquare_proj
#print axioms gluedMetricUnitSpinSquare_isCoveringMap
#print axioms gluedMetricUnitSpinSquare_two_distinct
#print axioms gluedMetricUnitSpinSquare_fiber_ncard
#print axioms liftPath_gluedMetricUnitFiberTurn_one_ne

end

end SystolicGrowth.ExerciseGluingPreparation
