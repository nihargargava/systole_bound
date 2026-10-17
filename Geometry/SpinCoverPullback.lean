module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingMetricSpinCover

@[expose] public section

/-!
# Genuine pullbacks of the constructed global spin covering

The pullback has the inherited subtype topology of the actual product. Its
local covering charts are derived from the given covering map's genuine
evenly covered neighborhoods. The geometric map from a universal-cover unit
tangent bundle remains a separate construction, not a field assumed here.
-/

open Set Topology Bundle
open scoped Manifold

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

section Pullback

variable {E B X : Type*}

/-- The actual topological pullback, not a separately postulated covering. -/
abbrev CoveringPullback (p : E → B) (f : X → B) :=
  {q : X × E // f q.1 = p q.2}

/-- The actual first-coordinate projection of the pullback carrier. -/
def coveringPullbackProjection (p : E → B) (f : X → B) : CoveringPullback p f → X :=
  fun q => q.val.1

/-- The actual second-coordinate map back into the original covering. -/
def coveringPullbackLift (p : E → B) (f : X → B) : CoveringPullback p f → E :=
  fun q => q.val.2

theorem coveringPullback_commutes (p : E → B) (f : X → B)
    (q : CoveringPullback p f) :
    f (coveringPullbackProjection p f q) = p (coveringPullbackLift p f q) := q.property

variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

omit [TopologicalSpace B] in
theorem continuous_coveringPullbackProjection (p : E → B) (f : X → B) :
    Continuous (coveringPullbackProjection p f) := continuous_fst.comp continuous_subtype_val

omit [TopologicalSpace B] in
theorem continuous_coveringPullbackLift (p : E → B) (f : X → B) :
    Continuous (coveringPullbackLift p f) := continuous_snd.comp continuous_subtype_val

/-- Pullback fibers are homeomorphic to the literal original covering fibers. -/
def coveringPullbackFiberHomeomorph (p : E → B) (f : X → B) (x : X) :
    (coveringPullbackProjection p f ⁻¹' {x}) ≃ₜ (p ⁻¹' {f x}) where
  toFun q := ⟨q.val.val.2, by
    change p q.val.val.2 = f x
    rw [← q.val.property]
    exact congrArg f q.property⟩
  invFun e := ⟨⟨(x, e.val), e.property.symm⟩, rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext q.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pulling back a genuine covering along a continuous map produces a
genuine covering in the inherited product-subtype topology. -/
theorem isCoveringMap_coveringPullbackProjection
    (p : E → B) (hp : IsCoveringMap p) (f : X → B) (hf : Continuous f) :
    IsCoveringMap (coveringPullbackProjection p f) := by
  intro x
  obtain ⟨hI, U, hxU, hU, hpU, H, hH⟩ := hp (f x)
  letI := hI
  have hlocal : IsEvenlyCovered (coveringPullbackProjection p f) x (p ⁻¹' {f x}) := by
    refine ⟨hI, f ⁻¹' U, hxU, hU.preimage hf,
      (hU.preimage hf).preimage (continuous_coveringPullbackProjection p f), ?_, ?_⟩
    · refine {
        toFun := fun q => (⟨q.val.val.1, q.property⟩,
          (H ⟨q.val.val.2, by
            change p q.val.val.2 ∈ U
            rw [← q.val.property]
            exact q.property⟩).2)
        invFun := fun xi =>
          ⟨⟨(xi.1.val, (H.symm (⟨f xi.1.val, xi.1.property⟩, xi.2)).val), by
            have hh := hH (H.symm (⟨f xi.1.val, xi.1.property⟩, xi.2))
            rw [H.apply_symm_apply] at hh
            exact hh⟩, xi.1.property⟩
        left_inv := ?_
        right_inv := ?_
        continuous_toFun := ?_
        continuous_invFun := ?_ }
      · intro q
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · let e : p ⁻¹' U := ⟨q.val.val.2, by
            change p q.val.val.2 ∈ U
            rw [← q.val.property]
            exact q.property⟩
          have hfirst : (H e).1 = ⟨f q.val.val.1, q.property⟩ := by
            apply Subtype.ext
            exact (hH e).trans q.val.property.symm
          have hh : (⟨f q.val.val.1, q.property⟩, (H e).2) = H e :=
            Prod.ext hfirst.symm rfl
          have he := congrArg H.symm hh
          rw [H.symm_apply_apply] at he
          exact congrArg Subtype.val he
      · intro xi
        change (xi.1, (H (H.symm (⟨f xi.1.val, xi.1.property⟩, xi.2))).2) = xi
        exact Prod.ext rfl
          (congrArg (fun z : U × (p ⁻¹' {f x}) => z.2)
            (H.apply_symm_apply (⟨f xi.1.val, xi.1.property⟩, xi.2)))
      · fun_prop
      · fun_prop
    · intro q
      rfl
  exact hlocal.to_isEvenlyCovered_preimage

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X] in
/-- Every actual pullback fiber is inhabited when the original cover is
surjective; no choice of new covering sheets is assumed. -/
theorem coveringPullbackProjection_surjective (p : E → B) (f : X → B)
    (hp : Function.Surjective p) : Function.Surjective (coveringPullbackProjection p f) := by
  intro x
  obtain ⟨e, he⟩ := hp (f x)
  exact ⟨⟨(x, e), he.symm⟩, rfl⟩

end Pullback

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {S : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera S)
  (m : ContinuousRiemannianMetric ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
  {X : Type*} (f : X → P.MetricUnitTangentCarrier m)

/-- Pullback of the internally constructed global metric spin cover along
an actual map into the metric's real unit tangent bundle. -/
abbrev MetricSpinPullback := CoveringPullback (P.gluedMetricUnitSpinSquare m) f

def metricSpinPullbackProjection : P.MetricSpinPullback m f → X :=
  coveringPullbackProjection (P.gluedMetricUnitSpinSquare m) f

def metricSpinPullbackLift : P.MetricSpinPullback m f → P.GluedSpinCarrier :=
  coveringPullbackLift (P.gluedMetricUnitSpinSquare m) f

theorem metricSpinPullback_commutes (q : P.MetricSpinPullback m f) :
    f (P.metricSpinPullbackProjection m f q) =
      P.gluedMetricUnitSpinSquare m (P.metricSpinPullbackLift m f q) := q.property

/-- This is a real producer from the proved global spin cover, not a new
spin-cover hypothesis on the universal-cover or half-plane model. -/
theorem metricSpinPullbackProjection_isCoveringMap [TopologicalSpace X] (hf : Continuous f) :
    IsCoveringMap (P.metricSpinPullbackProjection m f) :=
  isCoveringMap_coveringPullbackProjection (P.gluedMetricUnitSpinSquare m)
    (P.gluedMetricUnitSpinSquare_isCoveringMap m) f hf

theorem metricSpinPullbackProjection_surjective :
    Function.Surjective (P.metricSpinPullbackProjection m f) :=
  coveringPullbackProjection_surjective (P.gluedMetricUnitSpinSquare m) f
    (P.gluedMetricUnitSpinSquare_surjective m)

/-- The actual spin antipode lifts to the pullback without changing its
first coordinate or its image in the unit tangent bundle. -/
def metricSpinPullbackAntipode (q : P.MetricSpinPullback m f) : P.MetricSpinPullback m f :=
  ⟨(q.val.1, P.gluedSpinAntipode q.val.2), by
    rw [P.gluedMetricUnitSpinSquare_antipode]
    exact q.property⟩

@[simp] theorem metricSpinPullbackAntipode_proj (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackProjection m f (P.metricSpinPullbackAntipode m f q) =
      P.metricSpinPullbackProjection m f q := rfl

@[simp] theorem metricSpinPullbackAntipode_lift (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackLift m f (P.metricSpinPullbackAntipode m f q) =
      P.gluedSpinAntipode (P.metricSpinPullbackLift m f q) := rfl

theorem metricSpinPullbackAntipode_continuous [TopologicalSpace X] :
    Continuous (P.metricSpinPullbackAntipode m f) :=
  ((continuous_fst.comp continuous_subtype_val).prodMk
    (P.continuous_gluedSpinAntipode.comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _

@[simp] theorem metricSpinPullbackAntipode_involutive :
    Function.Involutive (P.metricSpinPullbackAntipode m f) := by
  intro q
  apply Subtype.ext
  exact Prod.ext rfl (P.gluedSpinAntipode_involutive q.val.2)

theorem metricSpinPullbackAntipode_ne (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackAntipode m f q ≠ q := by
  intro h
  exact P.gluedSpinAntipode_ne q.val.2
    (congrArg (fun r : P.MetricSpinPullback m f => r.val.2) h)

/-- The actual pullback projection has precisely the two original spin
points in each nonempty fiber, not an abstract replacement pair. -/
theorem metricSpinPullbackProjection_eq_iff (q r : P.MetricSpinPullback m f) :
    P.metricSpinPullbackProjection m f q = P.metricSpinPullbackProjection m f r ↔
      q = r ∨ q = P.metricSpinPullbackAntipode m f r := by
  constructor
  · intro h
    have hs : P.gluedMetricUnitSpinSquare m q.val.2 =
        P.gluedMetricUnitSpinSquare m r.val.2 :=
      q.property.symm.trans ((congrArg f h).trans r.property)
    rcases (P.gluedMetricUnitSpinSquare_eq_iff m q.val.2 r.val.2).mp hs with hs | hs
    · exact Or.inl (Subtype.ext (Prod.ext h hs))
    · exact Or.inr (Subtype.ext (Prod.ext h hs))
  · rintro (rfl | rfl)
    · rfl
    · rfl

theorem metricSpinPullbackProjection_fiber (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackProjection m f ⁻¹' {P.metricSpinPullbackProjection m f q} =
      {q, P.metricSpinPullbackAntipode m f q} := by
  ext r
  exact P.metricSpinPullbackProjection_eq_iff m f r q

theorem metricSpinPullbackProjection_two_distinct (x : X) :
    ∃ q : P.MetricSpinPullback m f,
      P.metricSpinPullbackProjection m f ⁻¹' {x} =
        {q, P.metricSpinPullbackAntipode m f q} ∧
          q ≠ P.metricSpinPullbackAntipode m f q := by
  obtain ⟨q, rfl⟩ := P.metricSpinPullbackProjection_surjective m f x
  exact ⟨q, P.metricSpinPullbackProjection_fiber m f q,
    (P.metricSpinPullbackAntipode_ne m f q).symm⟩

theorem metricSpinPullbackProjection_fiber_ncard (x : X) :
    (P.metricSpinPullbackProjection m f ⁻¹' {x}).ncard = 2 := by
  obtain ⟨q, hq, hne⟩ := P.metricSpinPullbackProjection_two_distinct m f x
  rw [hq]
  exact Set.ncard_pair hne

end ExerciseGluingPreparation

#print axioms coveringPullbackFiberHomeomorph
#print axioms isCoveringMap_coveringPullbackProjection
#print axioms ExerciseGluingPreparation.metricSpinPullbackProjection_isCoveringMap
#print axioms ExerciseGluingPreparation.metricSpinPullbackAntipode_involutive
#print axioms ExerciseGluingPreparation.metricSpinPullbackProjection_two_distinct
#print axioms ExerciseGluingPreparation.metricSpinPullbackProjection_fiber_ncard

end

end SystolicGrowth
