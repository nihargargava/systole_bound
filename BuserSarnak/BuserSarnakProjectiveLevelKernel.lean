module

public import BuserSarnak.BuserSarnakProjectiveLevelQuotient

@[expose] public section

/-!
# Comparing lifted and projective level kernels

The central scalar survives in the lifted finite quotient but is killed in the
projective finite quotient.  This module records the resulting bridge between
the two kernel presentations.  It is the group-theoretic prerequisite for
using a smaller projective Reidemeister--Schreier computation to mark the
same principal-level surface group.
-/

namespace SystolicGrowth

noncomputable section

/-- The presented lifted reduction has the expected value on each defining
generator. -/
@[simp] theorem buserSarnakOctagonReductionPresentedHom_of
    (p : ℕ) [NeZero p] (x : OctagonPresentationGenerator) :
    buserSarnakOctagonReductionPresentedHom p (PresentedGroup.of x) =
      buserSarnakOctagonReductionImage p x :=
  PresentedGroup.toGroup.of
    (buserSarnakOctagonReductionImage_relations p)

/-- Reducing the lifted scalar subgroup gives precisely the scalar subgroup
of the finite reduction image. -/
theorem liftedOctagonCenter_map_buserSarnakReduction
    (p : ℕ) [NeZero p] :
    liftedOctagonCenter.map (buserSarnakOctagonReductionPresentedHom p) =
      buserSarnakReductionCenterSubgroup p := by
  change (Subgroup.zpowers (PresentedGroup.of .z : LiftedOctagonGroup)).map
      (buserSarnakOctagonReductionPresentedHom p) =
    Subgroup.zpowers (buserSarnakOctagonReductionImage p .z)
  rw [MonoidHom.map_zpowers,
    buserSarnakOctagonReductionPresentedHom_of]

/-- The central generator of the lifted octagon group is nontrivial. -/
theorem liftedOctagon_z_ne_one :
    (PresentedGroup.of .z : LiftedOctagonGroup) ≠ 1 := by
  intro hz
  have hq := congrArg liftedOctagonToQuaternion hz
  have hcoord := congrArg BuserSarnakQuaternionUnit.x0 hq
  change (-1 : ℤ) = 1 at hcoord
  omega

/-- The lifted central generator has exact order two. -/
theorem orderOf_liftedOctagon_z :
    orderOf (PresentedGroup.of .z : LiftedOctagonGroup) = 2 := by
  exact orderOf_eq_prime liftedOctagon_z_sq liftedOctagon_z_ne_one

/-- Projecting an element of the lifted level kernel lands in the projective
level kernel. -/
def buserSarnakLiftedKernelToProjectiveKernel
    (p : ℕ) [NeZero p] :
    (buserSarnakOctagonReductionPresentedHom p).ker →*
      (buserSarnakProjectiveReductionPresentedHom p).ker where
  toFun x := ⟨liftedOctagonToProjective x, by
    change ((buserSarnakProjectiveReductionPresentedHom p).comp
      liftedOctagonToProjective) x = 1
    have hcomp := congrArg
      (fun f : LiftedOctagonGroup →* BuserSarnakProjectiveReductionRange p =>
        f x)
      (buserSarnakProjectiveReduction_comp_liftedOctagonToProjective p)
    rw [hcomp]
    change QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
        (buserSarnakOctagonReductionPresentedHom p x) = 1
    rw [x.property, map_one]⟩
  map_one' := Subtype.ext (liftedOctagonToProjective.map_one)
  map_mul' x y := Subtype.ext (liftedOctagonToProjective.map_mul x y)

@[simp] theorem buserSarnakLiftedKernelToProjectiveKernel_apply
    (p : ℕ) [NeZero p]
    (x : (buserSarnakOctagonReductionPresentedHom p).ker) :
    (buserSarnakLiftedKernelToProjectiveKernel p x : ProjectiveOctagonGroup) =
      liftedOctagonToProjective x := rfl

/-- Core.Reduction is injective on the central lifted scalar subgroup at every
odd prime level. -/
theorem liftedOctagonCenter_restrict_reduction_injective
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ x ∈ liftedOctagonCenter,
      buserSarnakOctagonReductionPresentedHom p x = 1 → x = 1 := by
  intro x hx hred
  rcases hx with ⟨n, rfl⟩
  rw [map_zpow, buserSarnakOctagonReductionPresentedHom_of] at hred
  have hdiv : (2 : ℤ) ∣ n := by
    simpa [orderOf_buserSarnakOctagonReductionImage_z p hp hp2] using
      (orderOf_dvd_iff_zpow_eq_one.mpr hred)
  apply orderOf_dvd_iff_zpow_eq_one.mp
  simpa [orderOf_liftedOctagon_z] using hdiv

/-- The lifted level kernel injects into the projective level kernel at an
odd prime. -/
theorem buserSarnakLiftedKernelToProjectiveKernel_injective
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (buserSarnakLiftedKernelToProjectiveKernel p) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hprojective : liftedOctagonToProjective (x : LiftedOctagonGroup) = 1 := by
    have hval := congrArg Subtype.val hx
    simpa [buserSarnakLiftedKernelToProjectiveKernel] using hval
  have hcenter : (x : LiftedOctagonGroup) ∈ liftedOctagonCenter := by
    rw [← liftedOctagonToProjective_ker]
    exact hprojective
  apply Subtype.ext
  exact liftedOctagonCenter_restrict_reduction_injective p hp hp2 x hcenter
    x.property

/-- Every projective level-kernel element has a lift in the lifted level
kernel: normalize an arbitrary lift by a central scalar power. -/
theorem buserSarnakLiftedKernelToProjectiveKernel_surjective
    (p : ℕ) [NeZero p] :
    Function.Surjective (buserSarnakLiftedKernelToProjectiveKernel p) := by
  intro y
  obtain ⟨x, hx⟩ := liftedOctagonToProjective_surjective (y : ProjectiveOctagonGroup)
  have hprojective :
      buserSarnakProjectiveReductionPresentedHom p
          (liftedOctagonToProjective x) = 1 := by
    rw [hx]
    exact y.property
  have hquotient :
      QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
          (buserSarnakOctagonReductionPresentedHom p x) = 1 := by
    have hcomp := congrArg
      (fun f : LiftedOctagonGroup →* BuserSarnakProjectiveReductionRange p => f x)
      (buserSarnakProjectiveReduction_comp_liftedOctagonToProjective p)
    change ((buserSarnakProjectiveReductionPresentedHom p).comp
      liftedOctagonToProjective) x = 1 at hprojective
    rw [hcomp] at hprojective
    exact hprojective
  obtain ⟨n, hn⟩ := (QuotientGroup.eq_one_iff _).mp hquotient
  let x' : LiftedOctagonGroup := x * (PresentedGroup.of .z : LiftedOctagonGroup) ^ (-n)
  have hx' : buserSarnakOctagonReductionPresentedHom p x' = 1 := by
    change buserSarnakOctagonReductionPresentedHom p
      (x * (PresentedGroup.of .z : LiftedOctagonGroup) ^ (-n)) = 1
    rw [map_mul, map_zpow, buserSarnakOctagonReductionPresentedHom_of, ← hn]
    group
  refine ⟨⟨x', hx'⟩, ?_⟩
  apply Subtype.ext
  change liftedOctagonToProjective x' = y
  dsimp [x']
  rw [map_mul, map_zpow, liftedOctagonToProjective_of,
    liftedOctagonToProjectiveGenerator, one_zpow, mul_one, hx]

/-- The central quotient identifies the lifted and projective finite level
kernels at every odd prime. -/
noncomputable def buserSarnakLiftedKernelEquivProjectiveKernel
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (buserSarnakOctagonReductionPresentedHom p).ker ≃*
      (buserSarnakProjectiveReductionPresentedHom p).ker :=
  MulEquiv.ofBijective (buserSarnakLiftedKernelToProjectiveKernel p)
    ⟨buserSarnakLiftedKernelToProjectiveKernel_injective p hp hp2,
      buserSarnakLiftedKernelToProjectiveKernel_surjective p⟩

end

end SystolicGrowth
