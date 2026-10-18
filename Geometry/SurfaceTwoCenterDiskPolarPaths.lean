module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureDiskVanKampen
public import Geometry.SurfaceTwoCenterSmallDiskConnector
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Literal polar loops and connector in the embedded local disk

This module packages the already-constructed small polar maps and cut
connector in the actual relative local-disk carrier of the open cover. Their
literal inclusions recover the original quotient maps and paths.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  {U : Set ℂ}

/-- A positive polar point in the actual component differs from both of the
original quotient centers, regardless of whether either center is active in
the endpoint component's puncture set. -/
private theorem twoCenterPolarPoint_ne_both_centers
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (b : Bool) (θ : Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ gluingRadius C g) :
    (Quotient.mk'' (gluingPolarPoint
      (if b then (P.centers i).1 else (P.centers i).2) θ ρ) : (X i).Carrier) ≠
        Quotient.mk'' (P.centers i).1 ∧
      (Quotient.mk'' (gluingPolarPoint
        (if b then (P.centers i).1 else (P.centers i).2) θ ρ) : (X i).Carrier) ≠
        Quotient.mk'' (P.centers i).2 := by
  let z : (X i).Carrier := Quotient.mk'' (gluingPolarPoint
    (if b then (P.centers i).1 else (P.centers i).2) θ ρ)
  let o : ℍ := if b then (P.centers i).1 else (P.centers i).2
  have hρR : ρ < gluingEmbeddedRadius C g :=
    lt_of_le_of_lt hρr P.radius_lt_embeddedRadius
  have hown : dist z (Quotient.mk'' o) = ρ := by
    rw [dist_comm]
    rw [(X i).carrier_dist_mk_center_eq_of_mem_closedBall o
      (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i)]
    · exact dist_gluingPolarPoint o θ hρ.le
    · change gluingPolarPoint o θ ρ ∈
        closedBall o (gluingEmbeddedRadius C g)
      rw [mem_closedBall]
      calc
        dist (gluingPolarPoint o θ ρ) o = dist o (gluingPolarPoint o θ ρ) :=
          dist_comm _ _
        _ = ρ := dist_gluingPolarPoint o θ hρ.le
        _ ≤ gluingEmbeddedRadius C g := hρR.le
  have houter : 0 < gluingEmbeddedRadius C g :=
    lt_trans P.radius_pos P.radius_lt_embeddedRadius
  have hseparation := P.carrier_centers_outer_add_inner_le_dist i
  cases b with
  | false =>
      have hownRight :
          dist z (Quotient.mk'' (P.centers i).2 : (X i).Carrier) = ρ := by
        simpa [z, o] using hown
      have htri := dist_triangle
        (Quotient.mk'' (P.centers i).1 : (X i).Carrier) z
        (Quotient.mk'' (P.centers i).2 : (X i).Carrier)
      have hfarLeft : gluingEmbeddedRadius C g ≤
          dist z (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
        calc
          gluingEmbeddedRadius C g ≤ dist (Quotient.mk'' (P.centers i).1 :
              (X i).Carrier) z := by
            nlinarith [hseparation, htri, hownRight, hρr]
          _ = dist z (Quotient.mk'' (P.centers i).1 : (X i).Carrier) :=
            dist_comm _ _
      constructor
      · intro heq
        have hz : dist z (Quotient.mk'' (P.centers i).1 : (X i).Carrier) = 0 := by
          simpa [z] using congrArg
            (fun x : (X i).Carrier => dist x
              (Quotient.mk'' (P.centers i).1 : (X i).Carrier)) heq
        linarith
      · intro heq
        have hz : dist z (Quotient.mk'' (P.centers i).2 : (X i).Carrier) = 0 := by
          simpa [z] using congrArg
            (fun x : (X i).Carrier => dist x
              (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) heq
        rw [hownRight] at hz
        linarith
  | true =>
      have hownLeft :
          dist z (Quotient.mk'' (P.centers i).1 : (X i).Carrier) = ρ := by
        simpa [z, o] using hown
      have htri := dist_triangle
        (Quotient.mk'' (P.centers i).1 : (X i).Carrier) z
        (Quotient.mk'' (P.centers i).2 : (X i).Carrier)
      have hleftz : dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) z = ρ := by
        rw [dist_comm]
        exact hownLeft
      have hfarRight : gluingEmbeddedRadius C g ≤
          dist z (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
        nlinarith [hseparation, htri, hleftz, hρr]
      constructor
      · intro heq
        have hz : dist z (Quotient.mk'' (P.centers i).1 : (X i).Carrier) = 0 := by
          simpa [z] using congrArg
            (fun x : (X i).Carrier => dist x
              (Quotient.mk'' (P.centers i).1 : (X i).Carrier)) heq
        rw [hownLeft] at hz
        linarith
      · intro heq
        have hz : dist z (Quotient.mk'' (P.centers i).2 : (X i).Carrier) = 0 := by
          simpa [z] using congrArg
            (fun x : (X i).Carrier => dist x
              (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) heq
        linarith

/-- The two-center open-cover ambient carrier includes into the original
native center-punctured component by the identity on quotient points. -/
theorem twoCenterAmbient_mem_native
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (z : embeddedTwoPunctureAmbientPoint f p q) :
    z.1 ∈ P.componentCenterPuncturedSet i := by
    rw [P.componentCenterPuncturedSet_eq i]
    change z.1 ∉
      ((if 0 < i.1 then {(Quotient.mk'' (P.centers i).1 : (X i).Carrier)} else ∅) ∪
        (if i.1 + 1 < n then
          {(Quotient.mk'' (P.centers i).2 : (X i).Carrier)} else ∅))
    intro hz
    rcases Set.mem_or_mem_of_mem_union hz with hleft | hright
    · by_cases hi : 0 < i.1
      · rw [if_pos hi] at hleft
        have heq := Set.mem_singleton_iff.mp hleft
        have hzambient := z.2
        change z.1 ≠ f p ∧ z.1 ≠ f q at hzambient
        exact hzambient.1 (heq.trans hp.symm)
      · simp [hi] at hleft
    · by_cases hi : i.1 + 1 < n
      · rw [if_pos hi] at hright
        have heq := Set.mem_singleton_iff.mp hright
        have hzambient := z.2
        change z.1 ≠ f p ∧ z.1 ≠ f q at hzambient
        exact hzambient.2 (heq.trans hq.symm)
      · simp [hi] at hright

def twoCenterAmbientToNativeComponent
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) :
    C(embeddedTwoPunctureAmbientPoint f p q,
      P.CenterPuncturedChainComponent i) where
  toFun z := ⟨z.1, P.twoCenterAmbient_mem_native i f p q hp hq z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk
    (fun z => P.twoCenterAmbient_mem_native i f p q hp hq z)

/-- A small polar point is in the two-center punctured ambient chart carrier,
using the exact original-center identities of the embedded chart. -/
theorem twoCenterPolarBoundaryPoint_ne_chartCenters
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (θ : Circle) :
    (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ≠ f p ∧
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ≠ f q := by
  have hne := P.twoCenterPolarPoint_ne_both_centers i b θ hρ hρr
  constructor
  · intro heq
    apply hne.1
    calc
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val = f p := heq
      _ = Quotient.mk'' (P.centers i).1 := hp
  · intro heq
    apply hne.2
    calc
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val = f q := heq
      _ = Quotient.mk'' (P.centers i).2 := hq

/-- The actual small polar map lands in the full punctured local-disk subtype.
The coordinate image comes from the small-circle chart witness, and both
deleted-center inequalities are proved from the original quotient metric. -/
noncomputable def twoCenterSmallPolarLocalDiskMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    C(Circle, {z : (X i).Carrier //
      z ∈ embeddedTwoPunctureLocalDisk f p q r}) where
  toFun θ := ⟨(P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val, by
    have himage : (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        f '' {z : U | ‖(z : ℂ)‖ < 1} := by
      simpa [embeddedCoordinatePunctureDisk] using hsmall b θ
    rcases himage with ⟨z, hz, hzx⟩
    have hne := P.twoCenterPolarBoundaryPoint_ne_chartCenters i f p q hp hq
      b ρ hρ hρr θ
    change ((P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        f '' {z : U | ‖(z : ℂ)‖ < r}) ∧
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedTwoPunctureAmbient f p q
    refine ⟨⟨z, lt_trans hz h1r, hzx⟩, ?_⟩
    change (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ≠ f p ∧
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ≠ f q
    exact hne⟩
  continuous_toFun := by
    apply (continuous_subtype_val.comp
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous).subtype_mk

def Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (x : P.CenterPuncturedChainComponent i) : Prop :=
  x.1 ≠ Quotient.mk'' (P.centers i).1 ∧
    x.1 ≠ Quotient.mk'' (P.centers i).2

private theorem path_trans_preserves_property
    {α : Type*} [TopologicalSpace α] {a b c : α}
    (γ : Path a b) (δ : Path b c) {D : Set α}
    (hγ : ∀ t, γ t ∈ D) (hδ : ∀ t, δ t ∈ D) :
    ∀ t, (γ.trans δ) t ∈ D := by
  intro t
  have ht : (γ.trans δ) t ∈ Set.range (γ.trans δ) := ⟨t, rfl⟩
  rw [Path.trans_range] at ht
  rcases ht with ht | ht
  · rcases ht with ⟨s, hs⟩
    rw [← hs]
    exact hγ s
  · rcases ht with ⟨s, hs⟩
    rw [← hs]
    exact hδ s

theorem twoCenterSmallPolarCandidate_avoids_both
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    ∀ t : I, Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i
      (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t) := by
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let leftArc := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true ρ hρ hρr).continuous
  let leftRad := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt θL
  let rightRad := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt θR
  let rightArc := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false ρ hρ hρr).continuous
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_left]
    exact (P.componentTwoCenterCutLeftAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_right]
    exact (P.componentTwoCenterCutRightAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  let core := ((P.componentTwoCenterCutArc i).map
      (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  let D : Set (P.CenterPuncturedChainComponent i) :=
    {x | Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i x}
  have hleftArc : ∀ t, leftArc t ∈ D := by
    intro t
    change Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i
      (P.twoCenterPolarBoundaryMap i true ρ hρ hρr ((Circle.path 1 θL) t))
    change _ ∧ _
    exact P.twoCenterPolarPoint_ne_both_centers i true
      ((Circle.path 1 θL) t) hρ hρr
  have hleftRad : ∀ t, leftRad t ∈ D := by
    intro t
    let s := (1 - (t : ℝ)) * ρ + (t : ℝ) * gluingRadius C g
    have hs : 0 < s := by
      dsimp [s]
      nlinarith [t.2.1, t.2.2, hρ]
    have hsr : s ≤ gluingRadius C g := by
      dsimp [s]
      nlinarith [t.2.1, t.2.2, hρr]
    have hne := P.twoCenterPolarPoint_ne_both_centers i true θL hs hsr
    change (P.twoCenterPolarPoint i true θL s hs hsr).val ≠
        Quotient.mk'' (P.centers i).1 ∧
      (P.twoCenterPolarPoint i true θL s hs hsr).val ≠
        Quotient.mk'' (P.centers i).2
    exact hne
  have hrightRad : ∀ t, rightRad t ∈ D := by
    intro t
    let s := (1 - (t : ℝ)) * gluingRadius C g + (t : ℝ) * ρ
    have hs : 0 < s := by
      dsimp [s]
      nlinarith [t.2.1, t.2.2, hρ]
    have hsr : s ≤ gluingRadius C g := by
      dsimp [s]
      nlinarith [t.2.1, t.2.2, hρr]
    have hne := P.twoCenterPolarPoint_ne_both_centers i false θR hs hsr
    change (P.twoCenterPolarPoint i false θR s hs hsr).val ≠
        Quotient.mk'' (P.centers i).1 ∧
      (P.twoCenterPolarPoint i false θR s hs hsr).val ≠
        Quotient.mk'' (P.centers i).2
    exact hne
  have hcore : ∀ t, core t ∈ D := by
    intro t
    change Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i
      (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t))
    change _ ∧ _
    constructor
    · intro heq
      have hdist := P.componentTwoCenterCutPoint_dist_left i t
      have hpositive : 0 < dist (P.componentTwoCenterCutPoint i t)
          (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
        rw [P.componentTwoCenterCutPoint_dist_left]
        nlinarith [P.carrier_centers_outer_add_inner_le_dist i,
          P.radius_pos, P.radius_lt_embeddedRadius, t.2.1]
      change P.componentTwoCenterCutPoint i t =
        Quotient.mk'' (P.centers i).1 at heq
      rw [heq, dist_self] at hpositive
      exact (lt_irrefl 0 hpositive)
    · intro heq
      have hpositive : 0 < dist (P.componentTwoCenterCutPoint i t)
          (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
        rw [P.componentTwoCenterCutPoint_dist_right]
        nlinarith [P.carrier_centers_outer_add_inner_le_dist i,
          P.radius_pos, P.radius_lt_embeddedRadius, t.2.2]
      change P.componentTwoCenterCutPoint i t =
        Quotient.mk'' (P.centers i).2 at heq
      rw [heq, dist_self] at hpositive
      exact (lt_irrefl 0 hpositive)
  have hrightArc : ∀ t, rightArc t ∈ D := by
    intro t
    change Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr ((Circle.path θR 1) t))
    change _ ∧ _
    exact P.twoCenterPolarPoint_ne_both_centers i false
      ((Circle.path θR 1) t) hρ hρr
  have hfirst := path_trans_preserves_property leftArc leftRad hleftArc hleftRad
  have hlast := path_trans_preserves_property core (rightRad.trans rightArc)
    hcore (path_trans_preserves_property rightRad rightArc hrightRad hrightArc)
  have hall := path_trans_preserves_property (leftArc.trans leftRad)
    (core.trans (rightRad.trans rightArc)) hfirst hlast
  intro t
  change Internal.SurfaceTwoCenterDiskPolarPathsHelpers.twoCenterAvoidsBothCenters P i
    (((leftArc.trans leftRad).trans (core.trans (rightRad.trans rightArc))) t)
  exact hall t

/-- The radius-angle candidate connector lifts to a path in the actual full
punctured local disk. Its coordinate-disk membership is the existing
candidate-containment theorem; both chart-center exclusions follow from its
literal polar and physical-cut pieces. -/
noncomputable def twoCenterSmallPolarLocalDiskConnector
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      embeddedCoordinatePunctureDisk f)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    Path
      (P.twoCenterSmallPolarLocalDiskMap i f p q r h1r hp hq
        true ρ hρ hρr hsmall 1)
      (P.twoCenterSmallPolarLocalDiskMap i f p q r h1r hp hq
        false ρ hρ hρr hsmall 1) := by
  let γ := P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
  have hcoord : ∀ t : I, (γ t).val ∈ embeddedCoordinatePunctureDisk f := by
    intro t
    exact P.componentTwoCenterSmallDiskConnectorCandidate_mem i ρ hρ hρr
      hsegment hsmall t
  have havoid := P.twoCenterSmallPolarCandidate_avoids_both i ρ hρ hρr
  have hmem : ∀ t : I, (γ t).val ∈ embeddedTwoPunctureLocalDisk f p q r := by
    intro t
    have himage : (γ t).val ∈ f '' {z : U | ‖(z : ℂ)‖ < 1} := by
      simpa [embeddedCoordinatePunctureDisk] using hcoord t
    rcases himage with ⟨z, hz, hzx⟩
    have hcenters := havoid t
    change (γ t).val ≠ Quotient.mk'' (P.centers i).1 ∧
      (γ t).val ≠ Quotient.mk'' (P.centers i).2 at hcenters
    change ((γ t).val ∈ f '' {z : U | ‖(z : ℂ)‖ < r}) ∧
      (γ t).val ∈ embeddedTwoPunctureAmbient f p q
    refine ⟨⟨z, lt_trans hz h1r, hzx⟩, ?_⟩
    change (γ t).val ≠ f p ∧ (γ t).val ≠ f q
    exact ⟨fun heq => hcenters.1 (heq.trans hp),
      fun heq => hcenters.2 (heq.trans hq)⟩
  refine ⟨⟨fun t => ⟨(γ t).val, hmem t⟩,
      (continuous_subtype_val.comp γ.continuous).subtype_mk hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    calc
      (γ 0).val = (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1).val :=
        congrArg Subtype.val γ.source
      _ = (twoCenterSmallPolarLocalDiskMap P i f p q r h1r hp hq
        true ρ hρ hρr hsmall 1).val := rfl
  · apply Subtype.ext
    calc
      (γ 1).val = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1).val :=
        congrArg Subtype.val γ.target
      _ = (twoCenterSmallPolarLocalDiskMap P i f p q r h1r hp hq
        false ρ hρ hρr hsmall 1).val := rfl

/-- The same small circle, now represented in the literal relative local-disk
member of the actual open cover. -/
noncomputable def twoCenterSmallPolarRelativeLocalDiskMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    C(Circle, {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}) := by
  let H := embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r
  let L := P.twoCenterSmallPolarLocalDiskMap i f p q r h1r hp hq b ρ hρ hρr hsmall
  exact ⟨fun θ => H.symm (L θ), H.symm.continuous.comp L.continuous⟩

/-- The actual relative-local-disk connector, transported through the
relative/full-disk homeomorphism. -/
noncomputable def twoCenterSmallPolarRelativeLocalDiskConnector
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      embeddedCoordinatePunctureDisk f)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    Path
      (twoCenterSmallPolarRelativeLocalDiskMap P i f p q r h1r hp hq
        true ρ hρ hρr hsmall 1)
      (twoCenterSmallPolarRelativeLocalDiskMap P i f p q r h1r hp hq
        false ρ hρ hρr hsmall 1) := by
  let H := embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r
  exact (P.twoCenterSmallPolarLocalDiskConnector i f p q r h1r hp hq
    ρ hρ hρr hsegment hsmall).map H.symm.continuous

/-- Forgetting the relative local-disk subtype sends the actual connector
back to the exact radius-angle candidate in the original native component. -/
theorem twoCenterSmallPolarRelativeLocalDiskConnector_native
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      embeddedCoordinatePunctureDisk f)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    ((P.twoCenterSmallPolarRelativeLocalDiskConnector i f p q r h1r hp hq
      ρ hρ hρr hsegment hsmall).map
      (((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).continuous)) =
    P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- The actual connector in the relative local disk represents the prescribed
cut connector after the literal inclusion into the original component. -/
theorem twoCenterSmallPolarRelativeLocalDiskConnector_homotopic_nativeCut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      embeddedCoordinatePunctureDisk f)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    ((P.twoCenterSmallPolarRelativeLocalDiskConnector i f p q r h1r hp hq
      ρ hρ hρr hsegment hsmall).map
      (((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).continuous)).Homotopic
      (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr) := by
  rw [P.twoCenterSmallPolarRelativeLocalDiskConnector_native i f p q r h1r
    hp hq ρ hρ hρr hsegment hsmall]
  exact (P.componentTwoCenterSmallPolarCutBasedPath_homotopic_candidate
    i ρ hρ hρr).symm

/-- The composite from the relative local disk to the original punctured
component is exactly the native small polar circle map. -/
theorem twoCenterSmallPolarRelativeLocalDiskMap_native
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    (P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
      ((twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)).comp
        (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
          b ρ hρ hρr hsmall)) =
      P.twoCenterPolarBoundaryMap i b ρ hρ hρr := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  rfl

/-- The relative-disk one-turn circle maps under the literal inclusion to
the original native small positive-polar one-turn loop, with no basepoint
change. -/
theorem twoCenterSmallPolarRelativeLocalDisk_oneTurn_map
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    ((circleOneTurnLoop 1).map
      (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
        b ρ hρ hρr hsmall).continuous).map
      (((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).continuous) =
    (circleOneTurnLoop 1).map
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous := by
  rw [Path.map_map]
  congr 1

/-- On fundamental groups, the literal relative local-disk inclusion sends
the small circle representative to the unchanged original component class. -/
theorem twoCenterSmallPolarRelativeLocalDisk_oneTurn_fundamentalGroup_map
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    FundamentalGroup.map
      ((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)))
      ((P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
        b ρ hρ hρr hsmall) 1)
      (Path.Homotopic.Quotient.mk
        ((circleOneTurnLoop 1).map
          (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
            b ρ hρ hρr hsmall).continuous)) =
    Path.Homotopic.Quotient.mk
      ((circleOneTurnLoop 1).map
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous) := by
  rw [FundamentalGroup.map_apply]
  exact congrArg Path.Homotopic.Quotient.mk
    (P.twoCenterSmallPolarRelativeLocalDisk_oneTurn_map i f p q r h1r hp hq
      b ρ hρ hρr hsmall)

/-- After literal inclusion into the original component, the relative-disk
positive one-turn class transports along the actual angle-one radius track to
the original gluing-radius positive peripheral loop. -/
theorem twoCenterSmallPolarRelativeLocalDisk_oneTurn_radius_transport
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ) (h1r : 1 < r)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (b : Bool) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (P.twoCenterPolarRadiusBasepointPath i b ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl)
      (FundamentalGroup.map
        ((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
          (twoOpenCoverAmalgamInclusion
            (embeddedTwoPunctureLocalDiskRelativeSide f p q r)))
        (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
          b ρ hρ hρr hsmall 1)
        (Path.Homotopic.Quotient.mk
          ((circleOneTurnLoop 1).map
            (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r hp hq
              b ρ hρ hρr hsmall).continuous))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((circleOneTurnLoop 1).map
            (P.twoCenterPolarBoundaryMap i b (gluingRadius C g)
              P.radius_pos le_rfl).continuous)) := by
  rw [P.twoCenterSmallPolarRelativeLocalDisk_oneTurn_fundamentalGroup_map
    i f p q r h1r hp hq b ρ hρ hρr hsmall]
  exact P.twoCenterPolarRadiusHomotopy_fundamentalGroup i b ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterPolarPoint_ne_both_centers
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterAmbientToNativeComponent
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterSmallPolarRelativeLocalDisk_oneTurn_map
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterSmallPolarRelativeLocalDisk_oneTurn_fundamentalGroup_map
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterSmallPolarRelativeLocalDiskConnector_native
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterSmallPolarRelativeLocalDiskConnector_homotopic_nativeCut
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterSmallPolarRelativeLocalDisk_oneTurn_radius_transport
