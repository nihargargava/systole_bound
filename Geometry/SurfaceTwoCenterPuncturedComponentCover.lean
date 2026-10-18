module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterDiskPolarPaths

@[expose] public section

/-!
# The internal native punctured-component carrier

For an internal component, its native punctured carrier and the actual
two-center open-cover ambient carrier delete exactly the same quotient
centers. This module identifies them by the identity on the original surface.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  {U : Set ℂ}

theorem internalCenterPuncturedSet_iff_ambient
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (x : (X i).Carrier) :
    x ∈ P.componentCenterPuncturedSet i ↔ x ∈ embeddedTwoPunctureAmbient f p q := by
  rw [P.componentCenterPuncturedSet_eq i]
  change x ∉
      ((if 0 < i.1 then {(Quotient.mk'' (P.centers i).1 : (X i).Carrier)} else ∅) ∪
        (if i.1 + 1 < n then
          {(Quotient.mk'' (P.centers i).2 : (X i).Carrier)} else ∅)) ↔
    x ≠ f p ∧ x ≠ f q
  rw [if_pos hi, if_pos hnext]
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨fun heq => hleft (heq.trans hp),
      fun heq => hright (heq.trans hq)⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨fun heq => hleft (heq.trans hp.symm),
      fun heq => hright (heq.trans hq.symm)⟩

/-- The internal native carrier is homeomorphic to the literal two-puncture
ambient subtype by the identity on quotient points. -/
def internalCenterPuncturedAmbientHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) :
    P.CenterPuncturedChainComponent i ≃ₜ embeddedTwoPunctureAmbientPoint f p q where
  toFun z := ⟨z.1,
    (P.internalCenterPuncturedSet_iff_ambient i f p q hi hnext hp hq z.1).mp z.2⟩
  invFun z := ⟨z.1,
    (P.internalCenterPuncturedSet_iff_ambient i f p q hi hnext hp hq z.1).mpr z.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := (P.twoCenterAmbientToNativeComponent i f p q hp hq).continuous

@[simp]
theorem internalCenterPuncturedAmbientHomeomorph_apply_val
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (z : P.CenterPuncturedChainComponent i) :
    (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq z).1 = z.1 := rfl

/-- The continuous inverse of the carrier homeomorphism is exactly the
already-constructed ambient-to-native map from the polar-path adapter. -/
theorem internalCenterPuncturedAmbientHomeomorph_inverse_continuousMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) :
    (⟨fun z => (P.internalCenterPuncturedAmbientHomeomorph
      i f p q hi hnext hp hq).symm z,
      (P.internalCenterPuncturedAmbientHomeomorph
        i f p q hi hnext hp hq).symm.continuous⟩ :
      C(embeddedTwoPunctureAmbientPoint f p q,
        P.CenterPuncturedChainComponent i)) =
      P.twoCenterAmbientToNativeComponent i f p q hp hq := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rfl

/-- The literal identity homeomorphism induces the based group equivalence
at each corresponding point of the two actual carriers. -/
noncomputable def internalCenterPuncturedFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (z : P.CenterPuncturedChainComponent i) :
    FundamentalGroup (P.CenterPuncturedChainComponent i) z ≃*
      FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q)
        (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq z) := by
  let e := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq
  let F := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  have hbij : Function.Bijective
      (FundamentalGroup.map ⟨e, e.continuous⟩ z) :=
    F.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk z) (FundamentalGroupoid.mk z)
  exact MulEquiv.ofBijective (FundamentalGroup.map ⟨e, e.continuous⟩ z) hbij

/-- On based loops, the group equivalence is induced by mapping the literal
native path through the identity-on-points homeomorphism. -/
theorem internalCenterPuncturedFundamentalGroupEquiv_apply_loop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (z : P.CenterPuncturedChainComponent i) (γ : Path z z) :
    P.internalCenterPuncturedFundamentalGroupEquiv i f p q hi hnext hp hq z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (γ.map (⟨P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq,
        (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq).continuous⟩ :
        C(P.CenterPuncturedChainComponent i,
          embeddedTwoPunctureAmbientPoint f p q)).continuous)) := by
  change FundamentalGroup.map
      (⟨P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq,
        (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq).continuous⟩ :
        C(P.CenterPuncturedChainComponent i,
          embeddedTwoPunctureAmbientPoint f p q)) z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = _
  rw [FundamentalGroup.map_apply]
  change (Path.Homotopic.Quotient.mk γ).map
      (⟨P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq,
        (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq).continuous⟩ :
        C(P.CenterPuncturedChainComponent i,
          embeddedTwoPunctureAmbientPoint f p q)) =
    Path.Homotopic.Quotient.mk (γ.map _)
  rw [← Path.Homotopic.Quotient.mk_map]

/-- Mapping a loop into the ambient carrier and back along the literal
inverse recovers the original based loop class. -/
theorem internalCenterPuncturedAmbientHomeomorph_roundTrip_loop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (z : P.CenterPuncturedChainComponent i) (γ : Path z z) :
    ((γ.map (⟨P.internalCenterPuncturedAmbientHomeomorph
      i f p q hi hnext hp hq,
      (P.internalCenterPuncturedAmbientHomeomorph
        i f p q hi hnext hp hq).continuous⟩ :
      C(P.CenterPuncturedChainComponent i,
        embeddedTwoPunctureAmbientPoint f p q)).continuous).map
      (P.twoCenterAmbientToNativeComponent i f p q hp hq).continuous) = γ := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse native-carrier equivalence carries every literally included
local-disk loop to its actual native inclusion. This is the exact based map
needed to transfer the marked annulus presentation to the original component. -/
theorem internalCenterPuncturedAmbientInverseEquiv_localLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (r : ℝ)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (loop : Path z z) :
    fundamentalGroupHomeomorphEquiv
      (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq).symm z.1
      (FundamentalGroup.map
        (twoOpenCoverAmalgamInclusion (embeddedTwoPunctureLocalDiskRelativeSide f p q r))
        z (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop))) =
      FundamentalGroup.map
        ((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
          (twoOpenCoverAmalgamInclusion
            (embeddedTwoPunctureLocalDiskRelativeSide f p q r)))
        z (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) := by
  let H := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq
  let J : C(embeddedTwoPunctureAmbientPoint f p q,
      P.CenterPuncturedChainComponent i) := ⟨H.symm, H.symm.continuous⟩
  let I := twoOpenCoverAmalgamInclusion
    (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
  let N := (P.twoCenterAmbientToNativeComponent i f p q hp hq).comp I
  change FundamentalGroup.map J z.1
    (FundamentalGroup.map I z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop))) =
    FundamentalGroup.map N z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop))
  have hI : FundamentalGroup.map I z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (loop.map I.continuous)) := by
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  have hJ : FundamentalGroup.map J z.1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loop.map I.continuous))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((loop.map I.continuous).map J.continuous)) := by
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  have hN : FundamentalGroup.map N z
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (loop.map N.continuous)) := by
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  rw [hI, hJ, hN]
  apply congrArg FundamentalGroup.fromPath
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.internalCenterPuncturedAmbientHomeomorph
#print axioms SystolicGrowth.ExerciseGluingPreparation.internalCenterPuncturedFundamentalGroupEquiv
#print axioms SystolicGrowth.ExerciseGluingPreparation.internalCenterPuncturedFundamentalGroupEquiv_apply_loop
#print axioms SystolicGrowth.ExerciseGluingPreparation.internalCenterPuncturedAmbientHomeomorph_roundTrip_loop
#print axioms SystolicGrowth.ExerciseGluingPreparation.internalCenterPuncturedAmbientInverseEquiv_localLoop
