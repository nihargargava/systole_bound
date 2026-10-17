module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCollarRetraction
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

/-!
# Based fundamental groups of the actual chain sides

At every point of an original closed prefix or suffix, its literal inclusion
and collar retraction induce inverse based group maps. The representative
loop homotopies are restrictions of the actual strong deformation retraction,
which fixes the entire original side, not merely a selected seam point.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Inclusion and retraction preserve each original prefix loop literally,
with only the endpoint casts supplied by the actual retraction identity. -/
theorem gluedChainPrefixRetraction_inclusion_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) (p : Path x x) :
    ((p.map (P.gluedChainPrefixInclusion k).continuous).map
      (P.gluedChainPrefixRetraction k).continuous).cast
        (P.gluedChainPrefixRetraction_inclusion k x).symm
        (P.gluedChainPrefixRetraction_inclusion k x).symm = p := by
  apply Path.ext
  funext t
  exact P.gluedChainPrefixRetraction_inclusion k (p t)

/-- The actual collar homotopy, reversed and restricted to a based loop.
Its endpoints remain fixed because the original basepoint lies in the
entire closed prefix fixed by the native strong deformation retraction. -/
def gluedChainPrefixInclusionRetractionLoopHomotopy
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k))
    (p : Path (P.gluedChainPrefixInclusion k x) (P.gluedChainPrefixInclusion k x)) :
    Path.Homotopy
      (((p.map (P.gluedChainPrefixRetraction k).continuous).cast
        (P.gluedChainPrefixRetraction_inclusion k x).symm
        (P.gluedChainPrefixRetraction_inclusion k x).symm).map
          (P.gluedChainPrefixInclusion k).continuous) p where
  toFun q := (P.gluedChainPrefixDeformationRetraction k).symm (q.1, p q.2)
  continuous_toFun := (P.gluedChainPrefixDeformationRetraction k).symm.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left := by
    intro t
    exact (P.gluedChainPrefixDeformationRetraction k).symm.apply_zero (p t)
  map_one_left := by
    intro t
    exact (P.gluedChainPrefixDeformationRetraction k).symm.apply_one (p t)
  prop' := by
    intro t u hu
    have hfix : (P.gluedChainPrefixDeformationRetraction k).symm
        (t, P.gluedChainPrefixInclusion k x) = P.gluedChainPrefixInclusion k x :=
      (P.gluedChainPrefixDeformationRetraction k).symm.eq_snd t x.2
    rcases hu with hu | hu
    · subst u
      change (P.gluedChainPrefixDeformationRetraction k).symm (t, p 0) =
        P.gluedChainPrefixInclusion k (P.gluedChainPrefixRetraction k (p 0))
      rw [p.source, P.gluedChainPrefixRetraction_inclusion]
      exact hfix
    · have hu : u = 1 := by simpa using hu
      subst u
      change (P.gluedChainPrefixDeformationRetraction k).symm (t, p 1) =
        P.gluedChainPrefixInclusion k (P.gluedChainPrefixRetraction k (p 1))
      rw [p.target, P.gluedChainPrefixRetraction_inclusion]
      exact hfix

/-- The based loop correspondence uses precisely the native relative
homotopy at the actual loop points and the reversed time parameter. -/
theorem gluedChainPrefixInclusionRetractionLoopHomotopy_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k))
    (p : Path (P.gluedChainPrefixInclusion k x) (P.gluedChainPrefixInclusion k x))
    (t u : unitInterval) :
    P.gluedChainPrefixInclusionRetractionLoopHomotopy k x p (t, u) =
      (P.gluedChainPrefixDeformationRetraction k).symm (t, p u) := rfl

theorem gluedChainPrefix_inclusion_retraction_loop_homotopic
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k))
    (p : Path (P.gluedChainPrefixInclusion k x) (P.gluedChainPrefixInclusion k x)) :
    (((p.map (P.gluedChainPrefixRetraction k).continuous).cast
      (P.gluedChainPrefixRetraction_inclusion k x).symm
      (P.gluedChainPrefixRetraction_inclusion k x).symm).map
        (P.gluedChainPrefixInclusion k).continuous).Homotopic p :=
  ⟨P.gluedChainPrefixInclusionRetractionLoopHomotopy k x p⟩

/-- The prefix equivalence is based at every original closed-prefix point.
Its forward map is the actual retraction; its inverse is the literal inclusion. -/
def gluedChainPrefixFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) :
    FundamentalGroup ↥(P.gluedChainPrefixNeighborhood k) (P.gluedChainPrefixInclusion k x) ≃*
      FundamentalGroup ↥(P.gluedChainPrefix k) x where
  toFun := FundamentalGroup.mapOfEq (P.gluedChainPrefixRetraction k)
    (P.gluedChainPrefixRetraction_inclusion k x)
  invFun := FundamentalGroup.map (P.gluedChainPrefixInclusion k) x
  left_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.eq]
    exact P.gluedChainPrefix_inclusion_retraction_loop_homotopic k x p
  right_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast, P.gluedChainPrefixRetraction_inclusion_loop]
  map_mul' := (FundamentalGroup.mapOfEq (P.gluedChainPrefixRetraction k)
    (P.gluedChainPrefixRetraction_inclusion k x)).map_mul

theorem gluedChainPrefixFundamentalGroupEquiv_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) :
    (P.gluedChainPrefixFundamentalGroupEquiv k x).toMonoidHom =
      FundamentalGroup.mapOfEq (P.gluedChainPrefixRetraction k)
        (P.gluedChainPrefixRetraction_inclusion k x) := rfl

theorem gluedChainPrefixFundamentalGroupEquiv_symm_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) :
    (P.gluedChainPrefixFundamentalGroupEquiv k x).symm.toMonoidHom =
      FundamentalGroup.map (P.gluedChainPrefixInclusion k) x := rfl

/-- Retraction gives the exact representative loop in the original prefix. -/
theorem gluedChainPrefixFundamentalGroupEquiv_apply_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k))
    (p : Path (P.gluedChainPrefixInclusion k x) (P.gluedChainPrefixInclusion k x)) :
    P.gluedChainPrefixFundamentalGroupEquiv k x ⟦p⟧ =
      ⟦(p.map (P.gluedChainPrefixRetraction k).continuous).cast
        (P.gluedChainPrefixRetraction_inclusion k x).symm
        (P.gluedChainPrefixRetraction_inclusion k x).symm⟧ := by
  exact FundamentalGroup.mapOfEq_apply (P.gluedChainPrefixRetraction k)
    (P.gluedChainPrefixRetraction_inclusion k x) ⟦p⟧

/-- The inverse equivalence includes each genuine original-prefix loop. -/
theorem gluedChainPrefixFundamentalGroupEquiv_symm_apply_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) (p : Path x x) :
    (P.gluedChainPrefixFundamentalGroupEquiv k x).symm ⟦p⟧ =
      ⟦p.map (P.gluedChainPrefixInclusion k).continuous⟧ := rfl

@[simp] theorem gluedChainPrefixFundamentalGroupEquiv_map_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) (p : Path x x) :
    P.gluedChainPrefixFundamentalGroupEquiv k x
      ⟦p.map (P.gluedChainPrefixInclusion k).continuous⟧ = ⟦p⟧ :=
  (P.gluedChainPrefixFundamentalGroupEquiv k x).apply_symm_apply ⟦p⟧

/-- Inclusion and retraction preserve each original suffix loop literally. -/
theorem gluedChainSuffixRetraction_inclusion_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) (p : Path x x) :
    ((p.map (P.gluedChainSuffixInclusion k).continuous).map
      (P.gluedChainSuffixRetraction k).continuous).cast
        (P.gluedChainSuffixRetraction_inclusion k x).symm
        (P.gluedChainSuffixRetraction_inclusion k x).symm = p := by
  apply Path.ext
  funext t
  exact P.gluedChainSuffixRetraction_inclusion k (p t)

/-- Restrict the reversed native suffix deformation retraction to the loop;
the entire original suffix, including its chosen basepoint, is fixed. -/
def gluedChainSuffixInclusionRetractionLoopHomotopy
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k))
    (p : Path (P.gluedChainSuffixInclusion k x) (P.gluedChainSuffixInclusion k x)) :
    Path.Homotopy
      (((p.map (P.gluedChainSuffixRetraction k).continuous).cast
        (P.gluedChainSuffixRetraction_inclusion k x).symm
        (P.gluedChainSuffixRetraction_inclusion k x).symm).map
          (P.gluedChainSuffixInclusion k).continuous) p where
  toFun q := (P.gluedChainSuffixDeformationRetraction k).symm (q.1, p q.2)
  continuous_toFun := (P.gluedChainSuffixDeformationRetraction k).symm.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left := by
    intro t
    exact (P.gluedChainSuffixDeformationRetraction k).symm.apply_zero (p t)
  map_one_left := by
    intro t
    exact (P.gluedChainSuffixDeformationRetraction k).symm.apply_one (p t)
  prop' := by
    intro t u hu
    have hfix : (P.gluedChainSuffixDeformationRetraction k).symm
        (t, P.gluedChainSuffixInclusion k x) = P.gluedChainSuffixInclusion k x :=
      (P.gluedChainSuffixDeformationRetraction k).symm.eq_snd t x.2
    rcases hu with hu | hu
    · subst u
      change (P.gluedChainSuffixDeformationRetraction k).symm (t, p 0) =
        P.gluedChainSuffixInclusion k (P.gluedChainSuffixRetraction k (p 0))
      rw [p.source, P.gluedChainSuffixRetraction_inclusion]
      exact hfix
    · have hu : u = 1 := by simpa using hu
      subst u
      change (P.gluedChainSuffixDeformationRetraction k).symm (t, p 1) =
        P.gluedChainSuffixInclusion k (P.gluedChainSuffixRetraction k (p 1))
      rw [p.target, P.gluedChainSuffixRetraction_inclusion]
      exact hfix

theorem gluedChainSuffixInclusionRetractionLoopHomotopy_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k))
    (p : Path (P.gluedChainSuffixInclusion k x) (P.gluedChainSuffixInclusion k x))
    (t u : unitInterval) :
    P.gluedChainSuffixInclusionRetractionLoopHomotopy k x p (t, u) =
      (P.gluedChainSuffixDeformationRetraction k).symm (t, p u) := rfl

theorem gluedChainSuffix_inclusion_retraction_loop_homotopic
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k))
    (p : Path (P.gluedChainSuffixInclusion k x) (P.gluedChainSuffixInclusion k x)) :
    (((p.map (P.gluedChainSuffixRetraction k).continuous).cast
      (P.gluedChainSuffixRetraction_inclusion k x).symm
      (P.gluedChainSuffixRetraction_inclusion k x).symm).map
        (P.gluedChainSuffixInclusion k).continuous).Homotopic p :=
  ⟨P.gluedChainSuffixInclusionRetractionLoopHomotopy k x p⟩

/-- The exact based suffix equivalence at every original closed-suffix point. -/
def gluedChainSuffixFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) :
    FundamentalGroup ↥(P.gluedChainSuffixNeighborhood k) (P.gluedChainSuffixInclusion k x) ≃*
      FundamentalGroup ↥(P.gluedChainSuffix k) x where
  toFun := FundamentalGroup.mapOfEq (P.gluedChainSuffixRetraction k)
    (P.gluedChainSuffixRetraction_inclusion k x)
  invFun := FundamentalGroup.map (P.gluedChainSuffixInclusion k) x
  left_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.eq]
    exact P.gluedChainSuffix_inclusion_retraction_loop_homotopic k x p
  right_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast, P.gluedChainSuffixRetraction_inclusion_loop]
  map_mul' := (FundamentalGroup.mapOfEq (P.gluedChainSuffixRetraction k)
    (P.gluedChainSuffixRetraction_inclusion k x)).map_mul

theorem gluedChainSuffixFundamentalGroupEquiv_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) :
    (P.gluedChainSuffixFundamentalGroupEquiv k x).toMonoidHom =
      FundamentalGroup.mapOfEq (P.gluedChainSuffixRetraction k)
        (P.gluedChainSuffixRetraction_inclusion k x) := rfl

theorem gluedChainSuffixFundamentalGroupEquiv_symm_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) :
    (P.gluedChainSuffixFundamentalGroupEquiv k x).symm.toMonoidHom =
      FundamentalGroup.map (P.gluedChainSuffixInclusion k) x := rfl

/-- The forward based map retains the actual retracted suffix-loop representative. -/
theorem gluedChainSuffixFundamentalGroupEquiv_apply_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k))
    (p : Path (P.gluedChainSuffixInclusion k x) (P.gluedChainSuffixInclusion k x)) :
    P.gluedChainSuffixFundamentalGroupEquiv k x ⟦p⟧ =
      ⟦(p.map (P.gluedChainSuffixRetraction k).continuous).cast
        (P.gluedChainSuffixRetraction_inclusion k x).symm
        (P.gluedChainSuffixRetraction_inclusion k x).symm⟧ := by
  exact FundamentalGroup.mapOfEq_apply (P.gluedChainSuffixRetraction k)
    (P.gluedChainSuffixRetraction_inclusion k x) ⟦p⟧

theorem gluedChainSuffixFundamentalGroupEquiv_symm_apply_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) (p : Path x x) :
    (P.gluedChainSuffixFundamentalGroupEquiv k x).symm ⟦p⟧ =
      ⟦p.map (P.gluedChainSuffixInclusion k).continuous⟧ := rfl

@[simp] theorem gluedChainSuffixFundamentalGroupEquiv_map_loop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) (p : Path x x) :
    P.gluedChainSuffixFundamentalGroupEquiv k x
      ⟦p.map (P.gluedChainSuffixInclusion k).continuous⟧ = ⟦p⟧ :=
  (P.gluedChainSuffixFundamentalGroupEquiv k x).apply_symm_apply ⟦p⟧

#print axioms gluedChainPrefixInclusionRetractionLoopHomotopy
#print axioms gluedChainPrefixFundamentalGroupEquiv
#print axioms gluedChainPrefixFundamentalGroupEquiv_map_loop
#print axioms gluedChainSuffixInclusionRetractionLoopHomotopy
#print axioms gluedChainSuffixFundamentalGroupEquiv
#print axioms gluedChainSuffixFundamentalGroupEquiv_map_loop

end

end SystolicGrowth.ExerciseGluingPreparation
