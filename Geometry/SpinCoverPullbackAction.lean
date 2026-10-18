module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SpinCoverPullback

@[expose] public section

/-!
# The natural coherent group action on an actual spin pullback

Deck invariance of the genuine defining unit-tangent map permits literal
reindexing of the first coordinate while retaining the original spin. The
group laws therefore hold before any classification by signed matrices.
No coherent holonomy lift or additional spin-cover data is assumed.
-/

open Set Topology Bundle
open scoped Manifold

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

section NaturalAction

variable {G E B X : Type*} [Group G] [MulAction G X]
  (p : E → B) (f : X → B) (hinv : ∀ (g : G) (x : X), f (g • x) = f x)

/-- The natural lift is literal reindexing, without selecting any spin sign. -/
def coveringPullbackAction (g : G) (q : CoveringPullback p f) : CoveringPullback p f :=
  ⟨(g • q.val.1, q.val.2), (hinv g q.val.1).trans q.property⟩

@[simp] theorem coveringPullbackAction_projection (g : G) (q : CoveringPullback p f) :
    coveringPullbackProjection p f (coveringPullbackAction p f hinv g q) =
      g • coveringPullbackProjection p f q := rfl

@[simp] theorem coveringPullbackAction_lift (g : G) (q : CoveringPullback p f) :
    coveringPullbackLift p f (coveringPullbackAction p f hinv g q) =
      coveringPullbackLift p f q := rfl

@[simp] theorem coveringPullbackAction_one (q : CoveringPullback p f) :
    coveringPullbackAction p f hinv (1 : G) q = q := by
  apply Subtype.ext
  exact Prod.ext (one_smul G q.val.1) rfl

/-- The actual pullback transformations are coherent under multiplication,
before their eventual identification with matrix actions. -/
theorem coveringPullbackAction_mul (g h : G) (q : CoveringPullback p f) :
    coveringPullbackAction p f hinv (g * h) q =
      coveringPullbackAction p f hinv g (coveringPullbackAction p f hinv h q) := by
  apply Subtype.ext
  exact Prod.ext (mul_smul g h q.val.1) rfl

/-- The genuine action structure on the actual pullback subtype. -/
@[instance_reducible]
def coveringPullbackMulAction : MulAction G (CoveringPullback p f) where
  smul := coveringPullbackAction p f hinv
  one_smul := coveringPullbackAction_one p f hinv
  mul_smul := coveringPullbackAction_mul p f hinv

@[simp] theorem coveringPullbackMulAction_smul (g : G) (q : CoveringPullback p f) :
    letI := coveringPullbackMulAction p f hinv
    g • q = coveringPullbackAction p f hinv g q := rfl

variable [TopologicalSpace E] [TopologicalSpace X]

/-- Every actual deck reindexing is continuous in the inherited product
topology as soon as the original deck transformation is continuous. -/
theorem coveringPullbackAction_continuous_const [ContinuousConstSMul G X] (g : G) :
    Continuous (coveringPullbackAction p f hinv g) := by
  apply Continuous.subtype_mk
  exact ((continuous_const_smul g).comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- Joint continuity is inherited from the genuine action on the source;
the actual spin coordinate remains unchanged. -/
theorem coveringPullbackAction_continuous [TopologicalSpace G] [ContinuousSMul G X] :
    Continuous (fun gq : G × CoveringPullback p f =>
      coveringPullbackAction p f hinv gq.1 gq.2) := by
  apply Continuous.subtype_mk
  exact (continuous_fst.smul
    (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))

theorem coveringPullbackMulAction_continuous_const [ContinuousConstSMul G X] :
    letI := coveringPullbackMulAction p f hinv
    ContinuousConstSMul G (CoveringPullback p f) := by
  letI := coveringPullbackMulAction p f hinv
  exact ⟨coveringPullbackAction_continuous_const p f hinv⟩

theorem coveringPullbackMulAction_continuous [TopologicalSpace G] [ContinuousSMul G X] :
    letI := coveringPullbackMulAction p f hinv
    ContinuousSMul G (CoveringPullback p f) := by
  letI := coveringPullbackMulAction p f hinv
  exact ⟨coveringPullbackAction_continuous p f hinv⟩

/-- Each actual group transformation lifts to a real pullback homeomorphism
with the genuine inverse transformation; no local inverse is selected. -/
def coveringPullbackActionHomeomorph [ContinuousConstSMul G X] (g : G) :
    CoveringPullback p f ≃ₜ CoveringPullback p f where
  toFun := coveringPullbackAction p f hinv g
  invFun := coveringPullbackAction p f hinv g⁻¹
  left_inv q := by
    rw [← coveringPullbackAction_mul p f hinv, inv_mul_cancel,
      coveringPullbackAction_one]
  right_inv q := by
    rw [← coveringPullbackAction_mul p f hinv, mul_inv_cancel,
      coveringPullbackAction_one]
  continuous_toFun := coveringPullbackAction_continuous_const p f hinv g
  continuous_invFun := coveringPullbackAction_continuous_const p f hinv g⁻¹

end NaturalAction

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {S : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera S)
  (m : ContinuousRiemannianMetric ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
  {G X : Type*} [Group G] [MulAction G X]
  (f : X → P.MetricUnitTangentCarrier m)
  (hinv : ∀ (g : G) (x : X), f (g • x) = f x)

/-- The actual natural group action on the internally constructed metric
spin pullback. Its second coordinate is the original, unchanged global spin. -/
def metricSpinPullbackAction (a : G) (q : P.MetricSpinPullback m f) :
    P.MetricSpinPullback m f :=
  coveringPullbackAction (P.gluedMetricUnitSpinSquare m) f hinv a q

/-- The true coherent action on the actual metric spin pullback. -/
@[instance_reducible]
def metricSpinPullbackMulAction : MulAction G (P.MetricSpinPullback m f) :=
  coveringPullbackMulAction (P.gluedMetricUnitSpinSquare m) f hinv

@[simp] theorem metricSpinPullbackAction_proj (a : G) (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackProjection m f (P.metricSpinPullbackAction m f hinv a q) =
      a • P.metricSpinPullbackProjection m f q := rfl

@[simp] theorem metricSpinPullbackAction_lift (a : G) (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackLift m f (P.metricSpinPullbackAction m f hinv a q) =
      P.metricSpinPullbackLift m f q := rfl

@[simp] theorem metricSpinPullbackAction_one (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackAction m f hinv (1 : G) q = q :=
  coveringPullbackAction_one (P.gluedMetricUnitSpinSquare m) f hinv q

theorem metricSpinPullbackAction_mul (a b : G) (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackAction m f hinv (a * b) q =
      P.metricSpinPullbackAction m f hinv a (P.metricSpinPullbackAction m f hinv b q) :=
  coveringPullbackAction_mul (P.gluedMetricUnitSpinSquare m) f hinv a b q

/-- The actual central spin involution commutes with every natural deck
transformation, because the latter leaves the original spin unchanged. -/
@[simp] theorem metricSpinPullbackAction_antipode (a : G) (q : P.MetricSpinPullback m f) :
    P.metricSpinPullbackAction m f hinv a (P.metricSpinPullbackAntipode m f q) =
      P.metricSpinPullbackAntipode m f (P.metricSpinPullbackAction m f hinv a q) := rfl

/-- Each pullback action lies over the same actual original metric unit
tangent after projection to the global spin covering. -/
@[simp] theorem metricSpinPullbackAction_square (a : G) (q : P.MetricSpinPullback m f) :
    P.gluedMetricUnitSpinSquare m
      (P.metricSpinPullbackLift m f (P.metricSpinPullbackAction m f hinv a q)) =
        P.gluedMetricUnitSpinSquare m (P.metricSpinPullbackLift m f q) := rfl

variable [TopologicalSpace X]

theorem metricSpinPullbackAction_continuous_const [ContinuousConstSMul G X] (a : G) :
    Continuous (P.metricSpinPullbackAction m f hinv a) :=
  coveringPullbackAction_continuous_const (P.gluedMetricUnitSpinSquare m) f hinv a

theorem metricSpinPullbackAction_continuous [TopologicalSpace G] [ContinuousSMul G X] :
    Continuous (fun aq : G × P.MetricSpinPullback m f =>
      P.metricSpinPullbackAction m f hinv aq.1 aq.2) :=
  coveringPullbackAction_continuous (P.gluedMetricUnitSpinSquare m) f hinv

/-- These are genuine homeomorphic deck lifts on the real metric spin
pullback, not an assumed group of signed-matrix lifts. -/
def metricSpinPullbackActionHomeomorph [ContinuousConstSMul G X] (a : G) :
    P.MetricSpinPullback m f ≃ₜ P.MetricSpinPullback m f :=
  coveringPullbackActionHomeomorph (P.gluedMetricUnitSpinSquare m) f hinv a

end ExerciseGluingPreparation

#print axioms coveringPullbackMulAction
#print axioms coveringPullbackAction_continuous
#print axioms coveringPullbackActionHomeomorph
#print axioms ExerciseGluingPreparation.metricSpinPullbackMulAction
#print axioms ExerciseGluingPreparation.metricSpinPullbackAction_mul
#print axioms ExerciseGluingPreparation.metricSpinPullbackAction_antipode
#print axioms ExerciseGluingPreparation.metricSpinPullbackActionHomeomorph

end

end SystolicGrowth
