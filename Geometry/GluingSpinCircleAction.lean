module

public import Geometry.GluingSpinChainCovering
public import Mathlib.Topology.CompactOpen

@[expose] public section

/-!
# Actual circle actions on the clutched spin cover

Literal phase multiplication descends through the component deck actions and
the genuine Fermi seam identifications. Squaring intertwines the two actions
by the degree-two circle map. The fiber turn below is lifted by the actual
covering map; tangent-atlas identification remains a separate construction.
-/

open UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane unitInterval

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

instance : MulAction Circle HalfPlaneSpinFrame where
  smul a q := ⟨q.point, a * q.phase⟩
  one_smul q := HalfPlaneSpinFrame.ext rfl (one_mul q.phase)
  mul_smul a b q := HalfPlaneSpinFrame.ext rfl (mul_assoc a b q.phase)

instance : MulAction Circle HalfPlaneTangentFrame where
  smul a q := ⟨q.point, a * q.phase⟩
  one_smul q := HalfPlaneTangentFrame.ext rfl (one_mul q.phase)
  mul_smul a b q := HalfPlaneTangentFrame.ext rfl (mul_assoc a b q.phase)

instance : ContinuousSMul Circle HalfPlaneSpinFrame where
  continuous_smul := continuous_induced_rng.mpr
    ((continuous_halfPlaneSpinFrame_point.comp continuous_snd).prodMk
      (continuous_fst.mul (continuous_halfPlaneSpinFrame_phase.comp continuous_snd)))

instance : ContinuousSMul Circle HalfPlaneTangentFrame where
  continuous_smul := continuous_induced_rng.mpr
    ((continuous_halfPlaneTangentFrame_point.comp continuous_snd).prodMk
      (continuous_fst.mul (continuous_halfPlaneTangentFrame_phase.comp continuous_snd)))

theorem halfPlaneSpinFrame_circle_smul_comm (a : Circle) (A : SL(2, ℝ))
    (q : HalfPlaneSpinFrame) : a • (A • q) = A • (a • q) := by
  apply HalfPlaneSpinFrame.ext
  · rfl
  · exact mul_left_comm _ _ _

theorem halfPlaneTangentFrame_circle_smul_comm (a : Circle) (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) : a • (A • q) = A • (a • q) := by
  apply HalfPlaneTangentFrame.ext
  · rfl
  · exact mul_left_comm _ _ _

theorem halfPlaneSpinSquare_circle_smul (a : Circle) (q : HalfPlaneSpinFrame) :
    halfPlaneSpinSquare (a • q) = a ^ 2 • halfPlaneSpinSquare q :=
  HalfPlaneTangentFrame.ext rfl (mul_pow _ _ _)

namespace ClosedHyperbolicSurface

variable {g : ℕ} (X : ClosedHyperbolicSurface g)

def spinCircleAction (a : Circle) : X.SpinCarrier → X.SpinCarrier :=
  Quotient.map' (a • ·) fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    change (A : SL(2, ℝ)) • (a • r) = a • q
    change (A : SL(2, ℝ)) • r = q at hA
    rw [← halfPlaneSpinFrame_circle_smul_comm, hA]

def tangentCircleAction (a : Circle) : X.TangentFrameCarrier → X.TangentFrameCarrier :=
  Quotient.map' (a • ·) fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    change (A : SL(2, ℝ)) • (a • r) = a • q
    change (A : SL(2, ℝ)) • r = q at hA
    rw [← halfPlaneTangentFrame_circle_smul_comm, hA]

instance : MulAction Circle X.SpinCarrier where
  smul := X.spinCircleAction
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h q => exact congrArg (Quotient.mk _) (one_smul Circle q)
  mul_smul a b q := by
    induction q using Quotient.inductionOn with
    | h q => exact congrArg (Quotient.mk _) (mul_smul a b q)

instance : MulAction Circle X.TangentFrameCarrier where
  smul := X.tangentCircleAction
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h q => exact congrArg (Quotient.mk _) (one_smul Circle q)
  mul_smul a b q := by
    induction q using Quotient.inductionOn with
    | h q => exact congrArg (Quotient.mk _) (mul_smul a b q)

instance : ContinuousSMul Circle X.SpinCarrier where
  continuous_smul := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp
      (continuous_fst.smul continuous_snd :
        Continuous (fun p : Circle × HalfPlaneSpinFrame => p.1 • p.2))

instance : ContinuousSMul Circle X.TangentFrameCarrier where
  continuous_smul := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp
      (continuous_fst.smul continuous_snd :
        Continuous (fun p : Circle × HalfPlaneTangentFrame => p.1 • p.2))

@[simp] theorem spinBase_circle_smul (a : Circle) (q : X.SpinCarrier) :
    X.spinBase (a • q) = X.spinBase q := by
  induction q using Quotient.inductionOn with
  | h q => rfl

@[simp] theorem tangentFrameBase_circle_smul (a : Circle) (q : X.TangentFrameCarrier) :
    X.tangentFrameBase (a • q) = X.tangentFrameBase q := by
  induction q using Quotient.inductionOn with
  | h q => rfl

theorem spinSquare_circle_smul (a : Circle) (q : X.SpinCarrier) :
    X.spinSquare (a • q) = a ^ 2 • X.spinSquare q := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (Quotient.mk _) (halfPlaneSpinSquare_circle_smul a q)

theorem spin_circle_smul_eq_self_iff (a : Circle) (q : X.SpinCarrier) :
    a • q = q ↔ a = 1 := by
  constructor
  · intro h
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
        (MulAction.orbitRel_apply.mp (Quotient.exact h))
      have hp : A • q.point = q.point := congrArg HalfPlaneSpinFrame.point hA
      have h1 := X.free A q.point hp
      subst A
      change (1 : SL(2, ℝ)) • q = a • q at hA
      have he := congrArg HalfPlaneSpinFrame.phase hA
      change halfPlaneSpinCircle 1 q.point * q.phase = a * q.phase at he
      rw [halfPlaneSpinCircle_one, one_mul] at he
      exact (mul_right_cancel (he.symm.trans (one_mul q.phase).symm))
  · rintro rfl
    exact one_smul Circle q

theorem tangent_circle_smul_eq_self_iff (a : Circle) (q : X.TangentFrameCarrier) :
    a • q = q ↔ a = 1 := by
  constructor
  · intro h
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
        (MulAction.orbitRel_apply.mp (Quotient.exact h))
      have hp : A • q.point = q.point := congrArg HalfPlaneTangentFrame.point hA
      have h1 := X.free A q.point hp
      subst A
      change (1 : SL(2, ℝ)) • q = a • q at hA
      have he := congrArg HalfPlaneTangentFrame.phase hA
      change halfPlaneSpinCircle 1 q.point ^ 2 * q.phase = a * q.phase at he
      rw [halfPlaneSpinCircle_one, one_pow, one_mul] at he
      exact (mul_right_cancel (he.symm.trans (one_mul q.phase).symm))
  · rintro rfl
    exact one_smul Circle q

def spinBoundaryCircleAction (o : ℍ) (ρ : ℝ) (a : Circle)
    (q : X.SpinBoundaryCarrier o ρ) : X.SpinBoundaryCarrier o ρ :=
  ⟨a • q.1, by simpa using q.2⟩

def tangentBoundaryCircleAction (o : ℍ) (ρ : ℝ) (a : Circle)
    (q : X.TangentBoundaryCarrier o ρ) : X.TangentBoundaryCarrier o ρ :=
  ⟨a • q.1, by simpa using q.2⟩

@[simp] theorem spinBoundaryCircleAction_param (o : ℍ) (ρ : ℝ)
    (a : Circle) (p : Circle × Circle) :
    X.spinBoundaryCircleAction o ρ a (X.spinBoundaryParam o ρ p) =
      X.spinBoundaryParam o ρ (p.1, a * p.2) := rfl

@[simp] theorem tangentBoundaryCircleAction_param (o : ℍ) (ρ : ℝ)
    (a : Circle) (p : Circle × Circle) :
    X.tangentBoundaryCircleAction o ρ a (X.tangentBoundaryParam o ρ p) =
      X.tangentBoundaryParam o ρ (p.1, a * p.2) := rfl

theorem fermiSpinBoundaryHomeomorph_circle_action {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (a : Circle) (q : XOut.SpinBoundaryCarrier oOut ρ) :
    XIn.spinBoundaryCircleAction oIn ρ a
      (fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut q) =
        fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
          (XOut.spinBoundaryCircleAction oOut ρ a q) := by
  obtain ⟨p, rfl⟩ := XOut.spinBoundaryParam_surjective oOut ρ q
  rw [spinBoundaryCircleAction_param, fermiSpinBoundaryHomeomorph_param,
    fermiSpinBoundaryHomeomorph_param, spinBoundaryCircleAction_param]
  apply congrArg (XIn.spinBoundaryParam oIn ρ)
  apply Prod.ext
  · rfl
  · exact mul_left_comm _ _ _

theorem fermiTangentBoundaryHomeomorph_circle_action {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (a : Circle) (q : XOut.TangentBoundaryCarrier oOut ρ) :
    XIn.tangentBoundaryCircleAction oIn ρ a
      (fermiTangentBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut q) =
        fermiTangentBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
          (XOut.tangentBoundaryCircleAction oOut ρ a q) := by
  obtain ⟨p, rfl⟩ := XOut.tangentBoundaryParam_surjective oOut ρ q
  rw [tangentBoundaryCircleAction_param, fermiTangentBoundaryHomeomorph_param,
    fermiTangentBoundaryHomeomorph_param, tangentBoundaryCircleAction_param]
  apply congrArg (XIn.tangentBoundaryParam oIn ρ)
  apply Prod.ext
  · rfl
  · exact mul_left_comm _ _ _

end ClosedHyperbolicSurface

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def spinChainComponentCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (a : Circle) (q : P.SpinChainComponent i) : P.SpinChainComponent i :=
  ⟨a • q.1, by simpa using q.2⟩

def tangentChainComponentCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (a : Circle) (q : P.TangentChainComponent i) : P.TangentChainComponent i :=
  ⟨a • q.1, by simpa using q.2⟩

def spinChainPieceCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) (q : P.SpinChainPieces) : P.SpinChainPieces :=
  ⟨q.1, P.spinChainComponentCircleAction q.1 a q.2⟩

def tangentChainPieceCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) (q : P.TangentChainPieces) : P.TangentChainPieces :=
  ⟨q.1, P.tangentChainComponentCircleAction q.1 a q.2⟩

theorem seamSpinHomeomorph_circle_action
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    (X (gluingChainEdgeRight k)).spinBoundaryCircleAction
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) a
        (P.seamSpinHomeomorph k q) =
          P.seamSpinHomeomorph k
            ((X (gluingChainEdgeLeft k)).spinBoundaryCircleAction
              (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) :=
  ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_circle_action _ _ _ _ _ _ _ _ _ a q

theorem seamTangentHomeomorph_circle_action
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    (X (gluingChainEdgeRight k)).tangentBoundaryCircleAction
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) a
        (P.seamTangentHomeomorph k q) =
          P.seamTangentHomeomorph k
            ((X (gluingChainEdgeLeft k)).tangentBoundaryCircleAction
              (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) :=
  ClosedHyperbolicSurface.fermiTangentBoundaryHomeomorph_circle_action _ _ _ _ _ _ _ _ _ a q

@[simp] theorem spinChainPieceCircleAction_seamSource
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceCircleAction a (P.spinSeamSource k q) = P.spinSeamSource k
      ((X (gluingChainEdgeLeft k)).spinBoundaryCircleAction
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) := rfl

@[simp] theorem spinChainPieceCircleAction_seamTarget
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceCircleAction a (P.spinSeamTarget k q) = P.spinSeamTarget k
      ((X (gluingChainEdgeLeft k)).spinBoundaryCircleAction
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change a • (P.seamSpinHomeomorph k q).1 = _
    exact congrArg Subtype.val (P.seamSpinHomeomorph_circle_action k a q)

@[simp] theorem tangentChainPieceCircleAction_seamSource
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.tangentChainPieceCircleAction a (P.tangentSeamSource k q) = P.tangentSeamSource k
      ((X (gluingChainEdgeLeft k)).tangentBoundaryCircleAction
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) := rfl

@[simp] theorem tangentChainPieceCircleAction_seamTarget
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : Circle)
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.tangentChainPieceCircleAction a (P.tangentSeamTarget k q) = P.tangentSeamTarget k
      ((X (gluingChainEdgeLeft k)).tangentBoundaryCircleAction
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) a q) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change a • (P.seamTangentHomeomorph k q).1 = _
    exact congrArg Subtype.val (P.seamTangentHomeomorph_circle_action k a q)

theorem spinChainRelation_circle_action (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) {q r : P.SpinChainPieces} (h : P.spinChainRelation q r) :
    P.spinChainRelation (P.spinChainPieceCircleAction a q)
      (P.spinChainPieceCircleAction a r) := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  rw [P.spinChainPieceCircleAction_seamSource, P.spinChainPieceCircleAction_seamTarget]
  exact ⟨k, _, rfl, rfl⟩

theorem tangentChainRelation_circle_action (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) {q r : P.TangentChainPieces} (h : P.tangentChainRelation q r) :
    P.tangentChainRelation (P.tangentChainPieceCircleAction a q)
      (P.tangentChainPieceCircleAction a r) := by
  obtain ⟨k, q, rfl, rfl⟩ := h
  rw [P.tangentChainPieceCircleAction_seamSource, P.tangentChainPieceCircleAction_seamTarget]
  exact ⟨k, _, rfl, rfl⟩

theorem eqvGen_spinChainRelation_circle_action
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle)
    {q r : P.SpinChainPieces} (h : Relation.EqvGen P.spinChainRelation q r) :
    Relation.EqvGen P.spinChainRelation (P.spinChainPieceCircleAction a q)
      (P.spinChainPieceCircleAction a r) := by
  induction h with
  | rel q r h => exact Relation.EqvGen.rel _ _ (P.spinChainRelation_circle_action a h)
  | refl q => exact Relation.EqvGen.refl _
  | symm q r h ih => exact Relation.EqvGen.symm _ _ ih
  | trans q r s hqr hrs ihqr ihrs => exact Relation.EqvGen.trans _ _ _ ihqr ihrs

theorem eqvGen_tangentChainRelation_circle_action
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle)
    {q r : P.TangentChainPieces} (h : Relation.EqvGen P.tangentChainRelation q r) :
    Relation.EqvGen P.tangentChainRelation (P.tangentChainPieceCircleAction a q)
      (P.tangentChainPieceCircleAction a r) := by
  induction h with
  | rel q r h => exact Relation.EqvGen.rel _ _ (P.tangentChainRelation_circle_action a h)
  | refl q => exact Relation.EqvGen.refl _
  | symm q r h ih => exact Relation.EqvGen.symm _ _ ih
  | trans q r s hqr hrs ihqr ihrs => exact Relation.EqvGen.trans _ _ _ ihqr ihrs

def gluedSpinCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) : P.GluedSpinCarrier → P.GluedSpinCarrier :=
  Quotient.map (P.spinChainPieceCircleAction a)
    fun _ _ h => P.eqvGen_spinChainRelation_circle_action a h

def gluedTangentCircleAction (P : ExerciseGluingPreparation C g n genera X)
    (a : Circle) : P.GluedTangentCarrier → P.GluedTangentCarrier :=
  Quotient.map (P.tangentChainPieceCircleAction a)
    fun _ _ h => P.eqvGen_tangentChainRelation_circle_action a h

instance (P : ExerciseGluingPreparation C g n genera X) : MulAction Circle P.GluedSpinCarrier where
  smul := P.gluedSpinCircleAction
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg (Quotient.mk _)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact one_smul Circle q.2.1
  mul_smul a b q := by
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg (Quotient.mk _)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact mul_smul a b q.2.1

instance (P : ExerciseGluingPreparation C g n genera X) :
    MulAction Circle P.GluedTangentCarrier where
  smul := P.gluedTangentCircleAction
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg (Quotient.mk _)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact one_smul Circle q.2.1
  mul_smul a b q := by
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg (Quotient.mk _)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact mul_smul a b q.2.1

theorem continuous_spinChainPieceCircleAction_uncurry
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous (fun p : Circle × P.SpinChainPieces => P.spinChainPieceCircleAction p.1 p.2) := by
  have hc : Continuous (fun p : Σ i, P.SpinChainComponent i × Circle =>
      (⟨p.1, P.spinChainComponentCircleAction p.1 p.2.2 p.2.1⟩ : P.SpinChainPieces)) := by
    apply continuous_sigma
    intro i
    have hs : Continuous (fun p : P.SpinChainComponent i × Circle => p.2 • p.1.1) :=
      continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
    have hs' : Continuous (fun p : P.SpinChainComponent i × Circle =>
        P.spinChainComponentCircleAction i p.2 p.1) :=
      hs.subtype_mk (fun p => by simpa using p.1.2)
    exact continuous_sigmaMk.comp hs'
  exact hc.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)

theorem continuous_tangentChainPieceCircleAction_uncurry
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous (fun p : Circle × P.TangentChainPieces =>
      P.tangentChainPieceCircleAction p.1 p.2) := by
  have hc : Continuous (fun p : Σ i, P.TangentChainComponent i × Circle =>
      (⟨p.1, P.tangentChainComponentCircleAction p.1 p.2.2 p.2.1⟩ :
        P.TangentChainPieces)) := by
    apply continuous_sigma
    intro i
    have hs : Continuous (fun p : P.TangentChainComponent i × Circle => p.2 • p.1.1) :=
      continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
    have hs' : Continuous (fun p : P.TangentChainComponent i × Circle =>
        P.tangentChainComponentCircleAction i p.2 p.1) :=
      hs.subtype_mk (fun p => by simpa using p.1.2)
    exact continuous_sigmaMk.comp hs'
  exact hc.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)

instance (P : ExerciseGluingPreparation C g n genera X) :
    ContinuousSMul Circle P.GluedSpinCarrier where
  continuous_smul := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp P.continuous_spinChainPieceCircleAction_uncurry

instance (P : ExerciseGluingPreparation C g n genera X) :
    ContinuousSMul Circle P.GluedTangentCarrier where
  continuous_smul := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp P.continuous_tangentChainPieceCircleAction_uncurry

@[simp] theorem gluedSpinBase_circle_smul
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle) (q : P.GluedSpinCarrier) :
    P.gluedSpinBase (a • q) = P.gluedSpinBase q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply congrArg (Quotient.mk _)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (X q.1).spinBase_circle_smul a q.2.1

@[simp] theorem gluedTangentBase_circle_smul
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle) (q : P.GluedTangentCarrier) :
    P.gluedTangentBase (a • q) = P.gluedTangentBase q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply congrArg (Quotient.mk _)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (X q.1).tangentFrameBase_circle_smul a q.2.1

/-- The actual global covering is equivariant for the literal degree-two
circle homomorphism. -/
theorem gluedSpinSquare_circle_smul
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle) (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare (a • q) = a ^ 2 • P.gluedSpinSquare q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply congrArg (Quotient.mk _)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (X q.1).spinSquare_circle_smul a q.2.1

theorem gluedSpin_circle_smul_eq_self_iff
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle) (q : P.GluedSpinCarrier) :
    a • q = q ↔ a = 1 := by
  constructor
  · intro h
    induction q using Quotient.inductionOn with
    | h q =>
      have he := P.gluedSpinMk_injective_component q.1 h
      exact ((X q.1).spin_circle_smul_eq_self_iff a q.2.1).mp
        (congrArg Subtype.val he)
  · rintro rfl
    exact one_smul Circle q

theorem gluedTangent_circle_smul_eq_self_iff
    (P : ExerciseGluingPreparation C g n genera X) (a : Circle) (q : P.GluedTangentCarrier) :
    a • q = q ↔ a = 1 := by
  constructor
  · intro h
    induction q using Quotient.inductionOn with
    | h q =>
      have he := P.gluedTangentMk_injective_component q.1 h
      exact ((X q.1).tangent_circle_smul_eq_self_iff a q.2.1).mp
        (congrArg Subtype.val he)
  · rintro rfl
    exact one_smul Circle q

@[simp] theorem gluedSpin_neg_one_circle_smul
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    (-1 : Circle) • q = P.gluedSpinAntipode q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply congrArg (Quotient.mk _)
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      change (-1 : Circle) • q.2.1 = (X q.1).spinAntipode q.2.1
      induction q.2.1 using Quotient.inductionOn with
      | h r =>
        apply congrArg (Quotient.mk _)
        apply HalfPlaneSpinFrame.ext
        · rfl
        · exact neg_one_mul r.phase

theorem Internal.GluingSpinCircleActionHelpers.circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.coe_injective
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  rfl

/-- The actual half-turn in the spin fiber, ending at its distinct antipode. -/
def spinFiberTurn (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedSpinCarrier) : Path q (P.gluedSpinAntipode q) where
  toFun t := Circle.exp (Real.pi * (t : ℝ)) • q
  continuous_toFun := (Circle.exp.continuous.comp
    (continuous_const.mul continuous_subtype_val)).smul continuous_const
  source' := by simp
  target' := by simp [Internal.GluingSpinCircleActionHelpers.circle_exp_pi]

/-- The literal once-around path in the actual clutched oriented-frame fiber. -/
def tangentFiberTurn (P : ExerciseGluingPreparation C g n genera X)
    (q : P.GluedTangentCarrier) : Path q q where
  toFun t := Circle.exp (2 * Real.pi * (t : ℝ)) • q
  continuous_toFun := (Circle.exp.continuous.comp
    (continuous_const.mul continuous_subtype_val)).smul continuous_const
  source' := by simp
  target' := by simp

@[simp] theorem gluedSpinSquare_spinFiberTurn
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) (t : I) :
    P.gluedSpinSquare (P.spinFiberTurn q t) =
      P.tangentFiberTurn (P.gluedSpinSquare q) t := by
  change P.gluedSpinSquare (Circle.exp (Real.pi * (t : ℝ)) • q) = _
  rw [P.gluedSpinSquare_circle_smul]
  congr 1
  rw [pow_two, ← Circle.exp_add]
  congr 1
  ring

/-- The genuine global covering lifts the once-around frame path to this
literal half-turn; no lift or monodromy is supplied as extra data. -/
theorem liftPath_tangentFiberTurn
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare_isCoveringMap.liftPath
      (P.tangentFiberTurn (P.gluedSpinSquare q)) q
      (P.tangentFiberTurn (P.gluedSpinSquare q)).source =
        (P.spinFiberTurn q : C(I, P.GluedSpinCarrier)) := by
  symm
  apply (P.gluedSpinSquare_isCoveringMap.eq_liftPath_iff'
    (P.tangentFiberTurn (P.gluedSpinSquare q)).source).mpr
  refine ⟨?_, (P.spinFiberTurn q).source⟩
  ext t
  exact P.gluedSpinSquare_spinFiberTurn q t

theorem liftPath_tangentFiberTurn_one
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare_isCoveringMap.liftPath
      (P.tangentFiberTurn (P.gluedSpinSquare q)) q
      (P.tangentFiberTurn (P.gluedSpinSquare q)).source 1 = P.gluedSpinAntipode q := by
  rw [P.liftPath_tangentFiberTurn]
  exact (P.spinFiberTurn q).target

theorem liftPath_tangentFiberTurn_one_ne
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedSpinSquare_isCoveringMap.liftPath
      (P.tangentFiberTurn (P.gluedSpinSquare q)) q
      (P.tangentFiberTurn (P.gluedSpinSquare q)).source 1 ≠ q := by
  rw [P.liftPath_tangentFiberTurn_one]
  exact P.gluedSpinAntipode_ne q

end ExerciseGluingPreparation

#print axioms ClosedHyperbolicSurface.spin_circle_smul_eq_self_iff
#print axioms ExerciseGluingPreparation.seamSpinHomeomorph_circle_action
#print axioms ExerciseGluingPreparation.continuous_spinChainPieceCircleAction_uncurry
#print axioms ExerciseGluingPreparation.gluedSpinSquare_circle_smul
#print axioms ExerciseGluingPreparation.gluedSpin_circle_smul_eq_self_iff
#print axioms ExerciseGluingPreparation.gluedTangent_circle_smul_eq_self_iff
#print axioms ExerciseGluingPreparation.liftPath_tangentFiberTurn
#print axioms ExerciseGluingPreparation.liftPath_tangentFiberTurn_one_ne

end

end SystolicGrowth
