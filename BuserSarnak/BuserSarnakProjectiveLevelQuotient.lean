module

public import BuserSarnak.BuserSarnakLevelPairing
public import BuserSarnak.BuserSarnakProjectiveCenter

@[expose] public section

/-!
# The finite projective Buser--Sarnak quotient

The lifted level quotient contains the nontrivial scalar image of `z`.  This
module divides by that central order-two subgroup.  The resulting quotient is
the natural state space for Reidemeister--Schreier reduction of the projective
orbifold presentation, with half as many states as the lifted presentation.
-/

namespace SystolicGrowth

noncomputable section

/-- The reduced central generator commutes with every element of the finite
reduction image. -/
theorem buserSarnakOctagonReductionImage_z_mem_center
    (p : ℕ) [NeZero p] :
    buserSarnakOctagonReductionImage p .z ∈
      Subgroup.center (BuserSarnakReductionRange p) := by
  rw [Subgroup.mem_center_iff]
  intro q
  rcases q.2 with ⟨u, hu⟩
  apply Subtype.ext
  change q.1 *
      (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
        (octagonUnit .center) =
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
        (octagonUnit .center) * q.1
  rw [← hu]
  rw [← map_mul, ← map_mul]
  exact congrArg
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
    (Subgroup.mem_center_iff.mp octagonQuaternion_center_mem_center u)

/-- The scalar subgroup in the finite reduction image. -/
abbrev buserSarnakReductionCenterSubgroup (p : ℕ) [NeZero p] :
    Subgroup (BuserSarnakReductionRange p) :=
  Subgroup.zpowers (buserSarnakOctagonReductionImage p .z)

instance buserSarnakReductionCenterSubgroup_normal
    (p : ℕ) [NeZero p] :
    (buserSarnakReductionCenterSubgroup p).Normal where
  conj_mem n hn g := by
    rcases hn with ⟨k, rfl⟩
    have hz : Commute g (buserSarnakOctagonReductionImage p .z) :=
      Subgroup.mem_center_iff.mp
        (buserSarnakOctagonReductionImage_z_mem_center p) g
    have hzpow := hz.zpow_right k
    have hconj :
        g * buserSarnakOctagonReductionImage p .z ^ k * g⁻¹ =
          buserSarnakOctagonReductionImage p .z ^ k := by
      rw [hzpow.eq]
      group
    rw [hconj]
    exact ⟨k, rfl⟩

/-- The finite reduction image after killing its scalar central involution. -/
abbrev BuserSarnakProjectiveReductionRange (p : ℕ) [NeZero p] :=
  BuserSarnakReductionRange p ⧸ buserSarnakReductionCenterSubgroup p

/-- At an odd prime, the reduced central generator has exact order two. -/
theorem orderOf_buserSarnakOctagonReductionImage_z
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (buserSarnakOctagonReductionImage p .z) = 2 := by
  apply orderOf_eq_prime (buserSarnakOctagonReductionImage_z_sq p)
  exact buserSarnakOctagonReductionImage_z_ne_one p hp hp2

/-- The reduced scalar subgroup has exactly two elements. -/
theorem natCard_buserSarnakReductionCenterSubgroup
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (buserSarnakReductionCenterSubgroup p) = 2 := by
  rw [Nat.card_zpowers,
    orderOf_buserSarnakOctagonReductionImage_z p hp hp2]

/-- The projective level quotient has exactly `halfImageIndex` states. -/
theorem natCard_buserSarnakProjectiveReductionRange
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Nat.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
  change Nat.card
      (BuserSarnakReductionRange p ⧸
        buserSarnakReductionCenterSubgroup p) = data.halfImageIndex
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (buserSarnakReductionCenterSubgroup p)
  rw [data.image_card_eq,
    natCard_buserSarnakReductionCenterSubgroup p hp hp2] at hcard
  omega

/-- Core.Reduction of a projective octagon generator into the finite projective
level quotient. -/
def buserSarnakProjectiveReductionImage (p : ℕ) [NeZero p] :
    ProjectiveOctagonGenerator → BuserSarnakProjectiveReductionRange p :=
  fun x => QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
    (buserSarnakOctagonReductionImage p
      (projectiveOctagonGeneratorLift x))

/-- Every defining relation of the projective octagon presentation vanishes
in the finite projective quotient. -/
lemma buserSarnakProjectiveReductionImage_relations
    (p : ℕ) [NeZero p] :
    ∀ r ∈ projectiveOctagonRelators,
      FreeGroup.lift (buserSarnakProjectiveReductionImage p) r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | e1_sq =>
      simp only [projectiveOctagonRelator, map_pow, FreeGroup.lift_apply_of]
      change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
        (buserSarnakOctagonReductionImage p .e1)) ^ 2 = 1
      rw [← map_pow,
        buserSarnakOctagonReductionImage_cone_sq p .e1 (by simp)]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  | e2_sq =>
      simp only [projectiveOctagonRelator, map_pow, FreeGroup.lift_apply_of]
      change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
        (buserSarnakOctagonReductionImage p .e2)) ^ 2 = 1
      rw [← map_pow,
        buserSarnakOctagonReductionImage_cone_sq p .e2 (by simp)]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  | e3_sq =>
      simp only [projectiveOctagonRelator, map_pow, FreeGroup.lift_apply_of]
      change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
        (buserSarnakOctagonReductionImage p .e3)) ^ 2 = 1
      rw [← map_pow,
        buserSarnakOctagonReductionImage_cone_sq p .e3 (by simp)]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  | e4_sq =>
      simp only [projectiveOctagonRelator, map_pow, FreeGroup.lift_apply_of]
      change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
        (buserSarnakOctagonReductionImage p .e4)) ^ 2 = 1
      rw [← map_pow,
        buserSarnakOctagonReductionImage_cone_sq p .e4 (by simp)]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  | polygon =>
      have hpolygon := buserSarnakOctagonReductionImage_relations p
        (octagonPresentationRelator .polygon)
        (⟨OctagonPresentationRelator.polygon, rfl⟩ :
          octagonPresentationRelator .polygon ∈ octagonPresentationRelators)
      simpa [projectiveOctagonRelator, octagonPresentationRelator,
        buserSarnakProjectiveReductionImage,
        projectiveOctagonGeneratorLift] using congrArg
          (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)) hpolygon

/-- The projective octagon group maps onto its finite level quotient. -/
def buserSarnakProjectiveReductionPresentedHom
    (p : ℕ) [NeZero p] :
    ProjectiveOctagonGroup →* BuserSarnakProjectiveReductionRange p :=
  PresentedGroup.toGroup (buserSarnakProjectiveReductionImage_relations p)

@[simp] theorem buserSarnakProjectiveReductionPresentedHom_of
    (p : ℕ) [NeZero p] (x : ProjectiveOctagonGenerator) :
    buserSarnakProjectiveReductionPresentedHom p (PresentedGroup.of x) =
      buserSarnakProjectiveReductionImage p x :=
  PresentedGroup.toGroup.of
    (buserSarnakProjectiveReductionImage_relations p)

/-- Projective finite reduction is exactly lifted finite reduction followed
by quotienting the central scalar. -/
theorem buserSarnakProjectiveReduction_comp_liftedOctagonToProjective
    (p : ℕ) [NeZero p] :
    (buserSarnakProjectiveReductionPresentedHom p).comp
        liftedOctagonToProjective =
      (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)).comp
        (buserSarnakOctagonReductionPresentedHom p) := by
  apply PresentedGroup.ext
  intro x
  cases x with
  | z =>
      simp only [MonoidHom.comp_apply, liftedOctagonToProjective_of,
        liftedOctagonToProjectiveGenerator, map_one,
        buserSarnakOctagonReductionPresentedHom, PresentedGroup.toGroup.of]
      symm
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  | a | c | e1 | e2 | e3 | e4 =>
      simp [liftedOctagonToProjectiveGenerator,
        buserSarnakProjectiveReductionImage,
        projectiveOctagonGeneratorLift,
        buserSarnakOctagonReductionPresentedHom,
        buserSarnakOctagonReductionImage]

/-- The projective octagon reduction reaches the entire finite projective
state space. -/
theorem buserSarnakProjectiveReductionPresentedHom_surjective
    (p : ℕ) [NeZero p] :
    Function.Surjective (buserSarnakProjectiveReductionPresentedHom p) := by
  intro q
  obtain ⟨qLift, rfl⟩ := QuotientGroup.mk'_surjective
    (N := buserSarnakReductionCenterSubgroup p) q
  obtain ⟨x, rfl⟩ :=
    buserSarnakOctagonReductionPresentedHom_surjective p qLift
  refine ⟨liftedOctagonToProjective x, ?_⟩
  exact DFunLike.congr_fun
    (buserSarnakProjectiveReduction_comp_liftedOctagonToProjective p) x

end

end SystolicGrowth
