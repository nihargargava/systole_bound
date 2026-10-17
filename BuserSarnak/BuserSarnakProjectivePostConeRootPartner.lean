module

public import BuserSarnak.BuserSarnakProjectivePostConeRawContour

@[expose] public section

/-!
# Opposite-sign pairing on the contracted root contour

The exact root-position equivalence identifies every literal position with
one physical source/target occurrence. The independent signed-position
equivalence identifies the same finite set with positive/negative letters.
This module packages the canonical opposite-sign partner permutation. The
one-orbit theorem needed for the complete Wicks certificate remains separate.
-/

namespace SystolicGrowth

noncomputable section

def Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap {X : Type*} : Sum X X → Sum X X :=
  Sum.elim Sum.inr Sum.inl

private theorem rootContourSumSwap_involutive {X : Type*} (x : Sum X X) :
    Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap x) = x := by
  cases x <;> rfl

private theorem rootContourSumSwap_eq_of_elim_eq_of_ne {X : Type*}
    (x y : Sum X X) (hlabel : x.elim id id = y.elim id id) (hne : x ≠ y) :
    x = Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap y := by
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          change a = b at hlabel
          subst b
          exact False.elim (hne rfl)
      | inr b =>
          change a = b at hlabel
          subst b
          rfl
  | inr a =>
      cases y with
      | inl b =>
          change a = b at hlabel
          subst b
          rfl
      | inr b =>
          change a = b at hlabel
          subst b
          exact False.elim (hne rfl)

/-- The signed positive/negative positions form an equivalence with the
literal positions of the contracted root contour. -/
noncomputable def canonicalProjectivePostConeRawRootContour_signedPositionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) ≃
      Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  Equiv.ofBijective
    (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2)
    (canonicalProjectivePostConeRawRootContour_signedPosition_bijective hp hp2)

@[simp] theorem canonicalProjectivePostConeRawRootContour_signedPositionEquiv_positive
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
      (Sum.inl z) = canonicalProjectivePostConeRawRootContourPositivePosition hp hp2 z :=
  rfl

@[simp] theorem canonicalProjectivePostConeRawRootContour_signedPositionEquiv_negative
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
      (Sum.inr z) = canonicalProjectivePostConeRawRootContourNegativePosition hp hp2 z :=
  rfl

/-- Pair each literal root-contour occurrence with the opposite signed
occurrence of the same retained generator. -/
noncomputable def canonicalProjectivePostConeRawRootContour_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
    (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap
      ((canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2).symm i))

/-- The opposite-sign pairing is a fixed-point-free involution. -/
theorem canonicalProjectivePostConeRawRootContour_partner_involutive
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Involutive (canonicalProjectivePostConeRawRootContour_partner hp hp2) := by
  let e := canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
  intro i
  cases h : e.symm i with
  | inl z =>
      have hi : i = e (Sum.inl z) := by
        rw [← h]
        exact (e.apply_symm_apply i).symm
      have hpartner : canonicalProjectivePostConeRawRootContour_partner hp hp2 i =
          e (Sum.inr z) := by
        change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm i)) = e (Sum.inr z)
        rw [h]
        rfl
      calc
        canonicalProjectivePostConeRawRootContour_partner hp hp2
            (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
            canonicalProjectivePostConeRawRootContour_partner hp hp2 (e (Sum.inr z)) := by
              rw [hpartner]
        _ = e (Sum.inl z) := by
          change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm (e (Sum.inr z)))) = e (Sum.inl z)
          rw [e.symm_apply_apply]
          rfl
        _ = i := hi.symm
  | inr z =>
      have hi : i = e (Sum.inr z) := by
        rw [← h]
        exact (e.apply_symm_apply i).symm
      have hpartner : canonicalProjectivePostConeRawRootContour_partner hp hp2 i =
          e (Sum.inl z) := by
        change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm i)) = e (Sum.inl z)
        rw [h]
        rfl
      calc
        canonicalProjectivePostConeRawRootContour_partner hp hp2
            (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
            canonicalProjectivePostConeRawRootContour_partner hp hp2 (e (Sum.inl z)) := by
              rw [hpartner]
        _ = e (Sum.inr z) := by
          change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm (e (Sum.inl z)))) = e (Sum.inr z)
          rw [e.symm_apply_apply]
          rfl
        _ = i := hi.symm

/-- The partner preserves the generator label and reverses the sign bit. -/
theorem canonicalProjectivePostConeRawRootContour_partner_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get
      (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
        (((canonicalProjectivePostConeRawRootContour hp hp2).get i).1,
          !((canonicalProjectivePostConeRawRootContour hp hp2).get i).2) := by
  let e := canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
  cases h : e.symm i with
  | inl z =>
      have hi : i = e (Sum.inl z) := by
        rw [← h]
        exact (e.apply_symm_apply i).symm
      have hpartner : canonicalProjectivePostConeRawRootContour_partner hp hp2 i =
          e (Sum.inr z) := by
        change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm i)) = e (Sum.inr z)
        rw [h]
        rfl
      rw [hpartner, hi,
        canonicalProjectivePostConeRawRootContour_signedPositionEquiv_positive,
        canonicalProjectivePostConeRawRootContour_signedPositionEquiv_negative,
        canonicalProjectivePostConeRawRootContourPositivePosition_spec,
        canonicalProjectivePostConeRawRootContourNegativePosition_spec]
      rfl

  | inr z =>
      have hi : i = e (Sum.inr z) := by
        rw [← h]
        exact (e.apply_symm_apply i).symm
      have hpartner : canonicalProjectivePostConeRawRootContour_partner hp hp2 i =
          e (Sum.inl z) := by
        change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm i)) = e (Sum.inl z)
        rw [h]
        rfl
      rw [hpartner, hi,
        canonicalProjectivePostConeRawRootContour_signedPositionEquiv_negative,
        canonicalProjectivePostConeRawRootContour_signedPositionEquiv_positive,
        canonicalProjectivePostConeRawRootContourNegativePosition_spec,
        canonicalProjectivePostConeRawRootContourPositivePosition_spec]
      rfl

/-- The provenance decoder retains an orientation bit in addition to the
literal signed letter. The partner reverses this bit at every position,
independently of whether that position was obtained from a selected source
or target witness. This is weaker than identifying the opposite physical
endpoint, since `EndpointSignedLetter` forgets the `Sum.inl`/`Sum.inr` tag. -/
theorem canonicalProjectivePostConeRawRootContour_partner_endpointSign
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      canonicalProjectivePostConeBoundarySideCycle
      (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
        (canonicalProjectivePostConeRawRootContour_partner hp hp2 i))).2 =
    !(canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      canonicalProjectivePostConeBoundarySideCycle
      (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2 i)).2 := by
  have hletters := canonicalProjectivePostConeRawRootContour_partner_spec hp hp2 i
  rw [canonicalProjectivePostConeRawRootContourPosition_endpoint_get hp hp2
      (canonicalProjectivePostConeRawRootContour_partner hp hp2 i),
    canonicalProjectivePostConeRawRootContourPosition_endpoint_get hp hp2 i] at hletters
  exact congrArg Prod.snd hletters

/-- At every contour position, the opposite-sign partner is the other
physical endpoint occurrence of the same retained generator. The endpoint
bijection rules out the same physical dart, while the partner specification
preserves the generator label. -/
theorem canonicalProjectivePostConeRawRootContour_partner_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2
        (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
      Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap
        (canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2 i) := by
  let d := canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2 i
  let d' := canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2
    (canonicalProjectivePostConeRawRootContour_partner hp hp2 i)
  have hnotfixed : canonicalProjectivePostConeRawRootContour_partner hp hp2 i ≠ i := by
    intro hfix
    have hget := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get hfix
    rw [canonicalProjectivePostConeRawRootContour_partner_spec hp hp2 i] at hget
    have hsign := congrArg Prod.snd hget
    cases ((canonicalProjectivePostConeRawRootContour hp hp2).get i).2 <;>
      simp at hsign
  have hdne : d' ≠ d := by
    intro hsame
    exact hnotfixed ((canonicalProjectivePostConeRawRootContourPosition_endpointEquiv
      hp hp2).injective hsame)
  have hletters := canonicalProjectivePostConeRawRootContour_partner_spec hp hp2 i
  rw [canonicalProjectivePostConeRawRootContourPosition_endpoint_get hp hp2
      (canonicalProjectivePostConeRawRootContour_partner hp hp2 i),
    canonicalProjectivePostConeRawRootContourPosition_endpoint_get hp hp2 i] at hletters
  have hlabels : d'.elim id id = d.elim id id := by
    simpa [d, d', canonicalProjectivePostConeRawRootContourPosition_endpoint,
      canonicalProjectivePostConeEndpointSignedLetter] using congrArg Prod.fst hletters
  change d' = Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap d
  exact rootContourSumSwap_eq_of_elim_eq_of_ne d' d hlabels hdne

/-- Exact signed-position exhaustion implies that no two root-contour
positions carry the same signed letter. -/
theorem canonicalProjectivePostConeRawRootContour_get_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeRawRootContour hp hp2).get := by
  let e := canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
  intro i j hij
  cases hi' : e.symm i with
  | inl x =>
    cases hj' : e.symm j with
    | inl y =>
        have hi : e (Sum.inl x) = i := by
          rw [← hi']
          exact e.apply_symm_apply i
        have hj : e (Sum.inl y) = j := by
          rw [← hj']
          exact e.apply_symm_apply j
        have hletters :
            (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inl x)) =
              (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inl y)) := by
          rw [hi, hj]
          exact hij
        change (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inl x)) =
            (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inl y))
          at hletters
        have hpair :=
          (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 x).symm.trans
            (hletters.trans
              (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 y))
        have hxy : x = y := by
          exact congrArg Prod.fst hpair
        subst y
        exact hi.symm.trans hj
    | inr y =>
        have hi : e (Sum.inl x) = i := by
          rw [← hi']
          exact e.apply_symm_apply i
        have hj : e (Sum.inr y) = j := by
          rw [← hj']
          exact e.apply_symm_apply j
        have hletters :
            (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inl x)) =
              (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inr y)) := by
          rw [hi, hj]
          exact hij
        change (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inl x)) =
            (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inr y))
          at hletters
        have hpair :=
          (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 x).symm.trans
            (hletters.trans
              (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 y))
        have hsign := congrArg Prod.snd hpair
        cases hsign
  | inr x =>
    cases hj' : e.symm j with
    | inl y =>
        have hi : e (Sum.inr x) = i := by
          rw [← hi']
          exact e.apply_symm_apply i
        have hj : e (Sum.inl y) = j := by
          rw [← hj']
          exact e.apply_symm_apply j
        have hletters :
            (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inr x)) =
              (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inl y)) := by
          rw [hi, hj]
          exact hij
        change (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inr x)) =
            (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inl y))
          at hletters
        have hpair :=
          (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 x).symm.trans
            (hletters.trans
              (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 y))
        have hsign := congrArg Prod.snd hpair
        cases hsign
    | inr y =>
        have hi : e (Sum.inr x) = i := by
          rw [← hi']
          exact e.apply_symm_apply i
        have hj : e (Sum.inr y) = j := by
          rw [← hj']
          exact e.apply_symm_apply j
        have hletters :
            (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inr x)) =
              (canonicalProjectivePostConeRawRootContour hp hp2).get (e (Sum.inr y)) := by
          rw [hi, hj]
          exact hij
        change (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inr x)) =
            (canonicalProjectivePostConeRawRootContour hp hp2).get
              (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 (Sum.inr y))
          at hletters
        have hpair :=
          (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 x).symm.trans
            (hletters.trans
              (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 y))
        have hxy : x = y := by
          exact congrArg Prod.fst hpair
        subst y
        exact hi.symm.trans hj

/-- If a physical endpoint is based at the root face, its canonical signed
occurrence position is decoded by the provenance map as that very endpoint,
with its physical source/target orientation. This identifies the two
independently constructed position witnesses using literal-letter
injectivity. -/
theorem canonicalProjectivePostConeRawRootContour_selectedPosition_endpoint_of_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      canonicalProjectivePostConeBoundarySideCycle
      (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
        (canonicalProjectivePostConeSurvivingDartPosition hp hp2 d)) =
      (d, canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) := by
  obtain ⟨tag, htag⟩ :=
    canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_current_dart
      hp hp2 d hface
  let e := canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
  let i := e.symm tag
  have hitag : e i = tag := e.apply_symm_apply tag
  have hi : i = canonicalProjectivePostConeSurvivingDartPosition hp hp2 d := by
    apply canonicalProjectivePostConeRawRootContour_get_injective hp hp2
    calc
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeEndpointSignedLetter hp hp2
            (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state
              canonicalProjectivePostConeBoundarySideCycle (e i) ) := by
          exact canonicalProjectivePostConeRawRootContourPosition_endpoint_get hp hp2 i
      _ = canonicalProjectivePostConeEndpointSignedLetter hp hp2
            (d, canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) :=
          congrArg (canonicalProjectivePostConeEndpointSignedLetter hp hp2)
            (hitag ▸ htag)
      _ = (canonicalProjectivePostConeRawRootContour hp hp2).get
            (canonicalProjectivePostConeSurvivingDartPosition hp hp2 d) := by
          rw [canonicalProjectivePostConeSurvivingDartPosition_spec hp hp2 d]
          cases d <;> rfl
  have he : e (canonicalProjectivePostConeSurvivingDartPosition hp hp2 d) = tag := by
    rw [← hi]
    exact e.apply_symm_apply tag
  simpa [e] using he ▸ htag

/-- The partner of a selected physical endpoint position is the selected
position for the opposite endpoint of the same retained generator. -/
theorem canonicalProjectivePostConeRawRootContour_partner_survivingDartPosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    canonicalProjectivePostConeRawRootContour_partner hp hp2
        (canonicalProjectivePostConeSurvivingDartPosition hp hp2 d) =
      canonicalProjectivePostConeSurvivingDartPosition hp hp2
        (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap d) := by
  let e := canonicalProjectivePostConeRawRootContour_signedPositionEquiv hp hp2
  cases d with
  | inl z =>
      change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm (e (Sum.inl z)))) = e (Sum.inr z)
      rw [e.symm_apply_apply]
      rfl
  | inr z =>
      change e (Internal.BuserSarnakProjectivePostConeRootPartnerHelpers.rootContourSumSwap (e.symm (e (Sum.inr z)))) = e (Sum.inl z)
      rw [e.symm_apply_apply]
      rfl

/-- Opposite signs prevent a root-contour position from partnering with
itself. -/
theorem canonicalProjectivePostConeRawRootContour_partner_ne
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeRawRootContour_partner hp hp2 i ≠ i := by
  intro h
  have hget := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get h
  rw [canonicalProjectivePostConeRawRootContour_partner_spec hp hp2 i] at hget
  have hsign := congrArg Prod.snd hget
  simp at hsign

/-- The canonical successor-after-partner rotation of root-contour
occurrences. -/
noncomputable def canonicalProjectivePostConeRawRootContour_rotation
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  cyclicSucc (canonicalProjectivePostConeRawRootContour_partner hp hp2 i)

/-- The partner is a bijection, since it is an involution. -/
theorem canonicalProjectivePostConeRawRootContour_partner_bijective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Bijective (canonicalProjectivePostConeRawRootContour_partner hp hp2) := by
  constructor
  · intro i j hij
    calc
      i = canonicalProjectivePostConeRawRootContour_partner hp hp2
          (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) :=
            (canonicalProjectivePostConeRawRootContour_partner_involutive hp hp2 i).symm
      _ = canonicalProjectivePostConeRawRootContour_partner hp hp2
          (canonicalProjectivePostConeRawRootContour_partner hp hp2 j) :=
            congrArg (canonicalProjectivePostConeRawRootContour_partner hp hp2) hij
      _ = j := canonicalProjectivePostConeRawRootContour_partner_involutive hp hp2 j
  · intro i
    exact ⟨canonicalProjectivePostConeRawRootContour_partner hp hp2 i,
      canonicalProjectivePostConeRawRootContour_partner_involutive hp hp2 i⟩

/-- The root-contour successor-after-partner rotation is a permutation. -/
theorem canonicalProjectivePostConeRawRootContour_rotation_bijective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Bijective (canonicalProjectivePostConeRawRootContour_rotation hp hp2) := by
  exact (cyclicSucc_bijective
    (canonicalProjectivePostConeRawRootContour hp hp2).length).comp
      (canonicalProjectivePostConeRawRootContour_partner_bijective hp hp2)

#print axioms canonicalProjectivePostConeRawRootContour_partner_involutive
#print axioms canonicalProjectivePostConeRawRootContour_partner_spec
#print axioms canonicalProjectivePostConeRawRootContour_partner_endpointSign
#print axioms canonicalProjectivePostConeRawRootContour_partner_endpoint
#print axioms canonicalProjectivePostConeRawRootContour_get_injective
#print axioms canonicalProjectivePostConeRawRootContour_selectedPosition_endpoint_of_root
#print axioms canonicalProjectivePostConeRawRootContour_partner_survivingDartPosition
#print axioms canonicalProjectivePostConeRawRootContour_partner_ne
#print axioms canonicalProjectivePostConeRawRootContour_rotation_bijective

end

end SystolicGrowth
