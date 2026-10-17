module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixSuffixRetraction
public import Geometry.GluingChainFundamentalGroup
public import Geometry.TwoPuncturedDiskFreePresentation

@[expose] public section

/-!
# Based groups for the retained right cover side

The actual right side of a later prefix cover retracts onto the closed
prefix/suffix intersection. At adjacent cuts this intersection is the
original retained component, with its literal quotient-carrier loops.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- View an actual point of the closed prefix/suffix intersection in the
pulled-back right side of the retained prefix cover. -/
def gluedChainPrefixRightCoverBasepoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) :
    ↥(P.gluedChainPrefixCoverSide k j false) :=
  P.gluedChainPrefixRightCoverSideInclusion k j x

/-- The actual restricted retraction followed by inclusion preserves every
loop based in the closed intersection, with the exact endpoint casts. -/
theorem gluedChainPrefixRightCoverSideRetraction_inclusion_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) (p : Path x x) :
    ((p.map (P.gluedChainPrefixRightCoverSideInclusion k j).continuous).map
      (P.gluedChainPrefixRightCoverSideRetraction k j hjk).continuous).cast
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm = p := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
  exact P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk (p t)

/-- The restricted suffix deformation gives the actual based loop homotopy
between inclusion after retraction and the original right-side loop. -/
def gluedChainPrefixRightCoverSideInclusionRetractionLoopHomotopy
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j))
    (p : Path (P.gluedChainPrefixRightCoverSideInclusion k j x)
      (P.gluedChainPrefixRightCoverSideInclusion k j x)) :
    Path.Homotopy
      (((p.map (P.gluedChainPrefixRightCoverSideRetraction k j hjk).continuous).cast
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm).map
          (P.gluedChainPrefixRightCoverSideInclusion k j).continuous) p where
  toFun q := (P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk).symm
    (q.1, p q.2)
  continuous_toFun := (P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk).symm.continuous.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left := by
    intro t
    exact (P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk).symm.apply_zero (p t)
  map_one_left := by
    intro t
    exact (P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk).symm.apply_one (p t)
  prop' := by
    intro t u hu
    let i := P.gluedChainPrefixRightCoverSideInclusion k j
    let r := P.gluedChainPrefixRightCoverSideRetraction k j hjk
    let D := P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk
    have hfix : D.symm (t, i x) = i x := D.symm.eq_snd t x.2.2
    rcases hu with hu | hu
    · subst u
      change D.symm (t, p 0) = i (r (p 0))
      rw [p.source]
      change D.symm (t, i x) = i (r (i x))
      change D.symm (t, i x) = i
        (P.gluedChainPrefixRightCoverSideRetraction k j hjk
          (P.gluedChainPrefixRightCoverSideInclusion k j x))
      rw [P.gluedChainPrefixRightCoverSideRetraction_inclusion]
      exact hfix
    · have hu : u = 1 := by simpa using hu
      subst u
      change D.symm (t, p 1) = i (r (p 1))
      rw [p.target]
      change D.symm (t, i x) = i (r (i x))
      change D.symm (t, i x) = i
        (P.gluedChainPrefixRightCoverSideRetraction k j hjk
          (P.gluedChainPrefixRightCoverSideInclusion k j x))
      rw [P.gluedChainPrefixRightCoverSideRetraction_inclusion]
      exact hfix

/-- Inclusion after retraction is based-homotopic to the original loop. -/
theorem gluedChainPrefixRightCoverSide_inclusion_retraction_loop_homotopic
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j))
    (p : Path (P.gluedChainPrefixRightCoverSideInclusion k j x)
      (P.gluedChainPrefixRightCoverSideInclusion k j x)) :
    (((p.map (P.gluedChainPrefixRightCoverSideRetraction k j hjk).continuous).cast
      (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm
      (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm).map
        (P.gluedChainPrefixRightCoverSideInclusion k j).continuous).Homotopic p :=
  ⟨P.gluedChainPrefixRightCoverSideInclusionRetractionLoopHomotopy k j hjk x p⟩

/-- The actual based equivalence from the restricted right open side to the
closed prefix/suffix intersection. Its maps are the literal restricted
collar retraction and inclusion. -/
def gluedChainPrefixRightCoverFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) :
    FundamentalGroup ↥(P.gluedChainPrefixCoverSide k j false)
      (P.gluedChainPrefixRightCoverSideInclusion k j x) ≃*
    FundamentalGroup ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) x where
  toFun := FundamentalGroup.mapOfEq
    (P.gluedChainPrefixRightCoverSideRetraction k j hjk)
    (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x)
  invFun := FundamentalGroup.map
    (P.gluedChainPrefixRightCoverSideInclusion k j) x
  left_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.eq]
    exact P.gluedChainPrefixRightCoverSide_inclusion_retraction_loop_homotopic
      k j hjk x p
  right_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast,
      P.gluedChainPrefixRightCoverSideRetraction_inclusion_loop]
  map_mul' := (FundamentalGroup.mapOfEq
    (P.gluedChainPrefixRightCoverSideRetraction k j hjk)
    (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x)).map_mul

/-- The forward based map sends a representative loop to its actual
retraction image, with only the endpoint casts furnished by the retraction
identity. -/
theorem gluedChainPrefixRightCoverFundamentalGroupEquiv_apply_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j))
    (p : Path (P.gluedChainPrefixRightCoverSideInclusion k j x)
      (P.gluedChainPrefixRightCoverSideInclusion k j x)) :
    P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j hjk x ⟦p⟧ =
      ⟦(p.map (P.gluedChainPrefixRightCoverSideRetraction k j hjk).continuous).cast
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm
        (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x).symm⟧ :=
  FundamentalGroup.mapOfEq_apply
    (P.gluedChainPrefixRightCoverSideRetraction k j hjk)
    (P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x) ⟦p⟧

/-- The inverse based map includes every literal loop in the closed
intersection into the actual right cover side. -/
theorem gluedChainPrefixRightCoverFundamentalGroupEquiv_symm_apply_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) (p : Path x x) :
    (P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j hjk x).symm ⟦p⟧ =
      ⟦p.map (P.gluedChainPrefixRightCoverSideInclusion k j).continuous⟧ := rfl

@[simp] theorem gluedChainPrefixRightCoverFundamentalGroupEquiv_map_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) (p : Path x x) :
    P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j hjk x
      ⟦p.map (P.gluedChainPrefixRightCoverSideInclusion k j).continuous⟧ = ⟦p⟧ :=
  (P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j hjk x).apply_symm_apply ⟦p⟧

/-- At adjacent cuts, the closed intersection is the original component. -/
def gluedChainPrefixRightCoverComponentFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (x : P.ChainComponent (gluingChainEdgeLeft k)) :
    FundamentalGroup ↥(P.gluedChainPrefixCoverSide k j false)
      (P.gluedChainPrefixRightCoverSideInclusion k j
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk x)) ≃*
    FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k)) x := by
  let hlt : j.val < k.val := by omega
  exact (P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j hlt
      (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk x)).trans
    (fundamentalGroupHomeomorphEquiv
      (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk) x).symm

/-- On an adjacent component, the inverse based map is the literal
component-to-intersection homeomorphism followed by inclusion into the
restricted right side. -/
theorem gluedChainPrefixRightCoverComponentFundamentalGroupEquiv_symm_apply_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (x : P.ChainComponent (gluingChainEdgeLeft k)) (p : Path x x) :
    (P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk x).symm
      ⟦p⟧ = ⟦(p.map (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk).continuous_toFun).map
        (P.gluedChainPrefixRightCoverSideInclusion k j).continuous⟧ := by
  let E := P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
  let y := E x
  let e : C(P.ChainComponent (gluingChainEdgeLeft k),
      ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) := ⟨E, E.continuous⟩
  change (P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j (by omega) y).symm
      ((fundamentalGroupHomeomorphEquiv E x) ⟦p⟧) = _
  have hE : fundamentalGroupHomeomorphEquiv E x ⟦p⟧ =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.map E.continuous_toFun)) := by
    change FundamentalGroup.map e x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) = _
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  rw [hE]
  change (P.gluedChainPrefixRightCoverFundamentalGroupEquiv k j (by omega) y).symm
      ⟦p.map E.continuous_toFun⟧ = _
  exact P.gluedChainPrefixRightCoverFundamentalGroupEquiv_symm_apply_loop
    k j (by omega) y (p.map E.continuous_toFun)

#print axioms gluedChainPrefixRightCoverBasepoint
#print axioms gluedChainPrefixRightCoverSideRetraction_inclusion_loop
#print axioms gluedChainPrefixRightCoverSideInclusionRetractionLoopHomotopy
#print axioms gluedChainPrefixRightCoverSide_inclusion_retraction_loop_homotopic
#print axioms gluedChainPrefixRightCoverFundamentalGroupEquiv
#print axioms gluedChainPrefixRightCoverFundamentalGroupEquiv_apply_loop
#print axioms gluedChainPrefixRightCoverFundamentalGroupEquiv_symm_apply_loop
#print axioms gluedChainPrefixRightCoverFundamentalGroupEquiv_map_loop
#print axioms gluedChainPrefixRightCoverComponentFundamentalGroupEquiv
#print axioms gluedChainPrefixRightCoverComponentFundamentalGroupEquiv_symm_apply_loop

end

end ExerciseGluingPreparation
end SystolicGrowth
