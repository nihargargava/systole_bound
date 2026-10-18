module

public import BuserSarnak.BuserSarnakProjectiveConeRelators

@[expose] public section

/-!
# Canonical pairs of projective cone edges

Each cone generator acts freely and involutively on finite projective level
states.  This module chooses one representative from every two-element orbit
and proves the exact cardinality needed for the first `2h` eliminations in the
projective Tietze certificate.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectiveConePairingRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- A deterministic ordering coordinate for finite projective quotient states. -/
noncomputable def buserSarnakProjectiveConeRank
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) : ℕ :=
  (Fintype.equivFin (BuserSarnakProjectiveReductionRange p) q).val

/-- The ordering coordinate distinguishes finite projective quotient states. -/
theorem buserSarnakProjectiveConeRank_injective
    (p : ℕ) [NeZero p] : Function.Injective (buserSarnakProjectiveConeRank p) := by
  intro q r h
  apply (Fintype.equivFin (BuserSarnakProjectiveReductionRange p)).injective
  apply Fin.ext
  exact h

/-- The state paired with `q` by the order-two action of a cone generator. -/
noncomputable def buserSarnakProjectiveConePartner
    (p : ℕ) [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) : BuserSarnakProjectiveReductionRange p :=
  (BuserSarnakProjectiveQuotientSectionData.canonicalBuserSarnakProjectiveConeSchreierData p).transition q e.lift

/-- The cone partner operation is involutive. -/
@[simp] theorem buserSarnakProjectiveConePartner_partner
    (p : ℕ) [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) :
    buserSarnakProjectiveConePartner p e
      (buserSarnakProjectiveConePartner p e q) = q := by
  simpa [buserSarnakProjectiveConePartner] using
    (canonicalBuserSarnakProjectiveQuotientSectionData p).cone_transition_twice q e

/-- At an odd prime, a cone partner is never the original state. -/
theorem buserSarnakProjectiveConePartner_ne
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) :
    buserSarnakProjectiveConePartner p e q ≠ q := by
  rw [buserSarnakProjectiveConePartner,
    canonicalBuserSarnakProjective_transition_eq_mul]
  exact buserSarnakProjectiveReductionImage_cone_right_fixedPointFree
    p hp hp2 q e.lift e.lift_isCone

/-- The cone partner action as a self-equivalence of projective quotient states. -/
noncomputable def buserSarnakProjectiveConePartnerEquiv
    (p : ℕ) [NeZero p]
    (e : ProjectiveOctagonConeGenerator) :
    BuserSarnakProjectiveReductionRange p ≃ BuserSarnakProjectiveReductionRange p where
  toFun := buserSarnakProjectiveConePartner p e
  invFun := buserSarnakProjectiveConePartner p e
  left_inv := buserSarnakProjectiveConePartner_partner p e
  right_inv := buserSarnakProjectiveConePartner_partner p e

/-- The lower-ranked endpoint in a two-state cone orbit. -/
noncomputable def buserSarnakProjectiveConeLower
    (p : ℕ) [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) : BuserSarnakProjectiveReductionRange p :=
  if buserSarnakProjectiveConeRank p q <
      buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q) then q
  else buserSarnakProjectiveConePartner p e q

/-- One chosen endpoint from each orbit of a cone involution. -/
def BuserSarnakProjectiveConePairRepresentative
    (p : ℕ) [NeZero p] (e : ProjectiveOctagonConeGenerator) :=
  {q : BuserSarnakProjectiveReductionRange p //
    buserSarnakProjectiveConeRank p q <
      buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q)}

noncomputable local instance buserSarnakProjectiveConePairRepresentativeFintype
    (p : ℕ) [NeZero p] (e : ProjectiveOctagonConeGenerator) :
    Fintype (BuserSarnakProjectiveConePairRepresentative p e) :=
  Fintype.subtype
    (Finset.univ.filter fun q : BuserSarnakProjectiveReductionRange p =>
      buserSarnakProjectiveConeRank p q <
        buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q))
    (by simp)

/-- The lower endpoint satisfies the representative predicate. -/
theorem buserSarnakProjectiveConeLower_lt_partner
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) :
    buserSarnakProjectiveConeRank p (buserSarnakProjectiveConeLower p e q) <
      buserSarnakProjectiveConeRank p
        (buserSarnakProjectiveConePartner p e (buserSarnakProjectiveConeLower p e q)) := by
  rw [buserSarnakProjectiveConeLower]
  split_ifs with h
  · exact h
  · have hrankNe :
        buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q) ≠
          buserSarnakProjectiveConeRank p q := by
      intro hrank
      apply buserSarnakProjectiveConePartner_ne p hp hp2 e q
      exact buserSarnakProjectiveConeRank_injective p hrank
    have hlt :
        buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q) <
          buserSarnakProjectiveConeRank p q :=
      lt_of_le_of_ne (Nat.le_of_not_gt h) hrankNe
    simpa [buserSarnakProjectiveConePartner_partner] using hlt

/-- The Boolean coordinate recording which endpoint of a cone orbit is used. -/
noncomputable def buserSarnakProjectiveConeSide
    (p : ℕ) [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveReductionRange p) : Bool :=
  if buserSarnakProjectiveConeRank p q <
      buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q) then false
  else true

/-- Every projective state is uniquely a cone-pair representative plus a
Boolean side. -/
noncomputable def buserSarnakProjectiveConePairEquiv
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator) :
    BuserSarnakProjectiveReductionRange p ≃
      BuserSarnakProjectiveConePairRepresentative p e × Bool where
  toFun q :=
    (⟨buserSarnakProjectiveConeLower p e q,
      buserSarnakProjectiveConeLower_lt_partner p hp hp2 e q⟩,
      buserSarnakProjectiveConeSide p e q)
  invFun qb := if qb.2 then buserSarnakProjectiveConePartner p e qb.1.1 else qb.1.1
  left_inv q := by
    by_cases h : buserSarnakProjectiveConeRank p q <
        buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q)
    · simp [buserSarnakProjectiveConeLower, buserSarnakProjectiveConeSide, h]
    · simp [buserSarnakProjectiveConeLower, buserSarnakProjectiveConeSide, h]
  right_inv qb := by
    rcases qb with ⟨⟨q, hq⟩, side⟩
    cases side
    · simp [buserSarnakProjectiveConeLower, buserSarnakProjectiveConeSide, hq]
    · have hreverse : ¬buserSarnakProjectiveConeRank p
          (buserSarnakProjectiveConePartner p e q) <
            buserSarnakProjectiveConeRank p q :=
        Nat.not_lt_of_ge hq.le
      simp [buserSarnakProjectiveConeLower, buserSarnakProjectiveConeSide,
        hreverse, buserSarnakProjectiveConePartner_partner]

/-- Each of the four cone involutions has exactly half as many state-orbits as
projective quotient states. -/
theorem card_buserSarnakProjectiveConePairRepresentative
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (e : ProjectiveOctagonConeGenerator) :
    Fintype.card (BuserSarnakProjectiveConePairRepresentative p e) =
      data.halfImageIndex / 2 := by
  have hcard := Fintype.card_congr
    (buserSarnakProjectiveConePairEquiv p hp hp2 e)
  have hq : Fintype.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
    simpa only [← Nat.card_eq_fintype_card] using
      natCard_buserSarnakProjectiveReductionRange hp hp2 data
  rw [Fintype.card_prod, Fintype.card_bool, hq] at hcard
  omega

/-- Index type for all four families of unordered projective cone-edge pairs. -/
abbrev BuserSarnakProjectiveConePairIndex
    (p : ℕ) [NeZero p] :=
  Σ e : ProjectiveOctagonConeGenerator,
    BuserSarnakProjectiveConePairRepresentative p e

/-- The four cone involutions provide exactly `2h` disjoint edge-orbits when
the projective quotient has `h` states.  These are the first-stage Tietze
elimination slots. -/
theorem card_buserSarnakProjectiveConePairIndex
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (BuserSarnakProjectiveConePairIndex p) =
      2 * data.halfImageIndex := by
  have hq : Fintype.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
    simpa only [← Nat.card_eq_fintype_card] using
      natCard_buserSarnakProjectiveReductionRange hp hp2 data
  have htwo := Fintype.card_congr
    (buserSarnakProjectiveConePairEquiv p hp hp2 .e1)
  rw [Fintype.card_prod, Fintype.card_bool, hq] at htwo
  have hrep := card_buserSarnakProjectiveConePairRepresentative hp hp2 data
    ProjectiveOctagonConeGenerator.e1
  rw [hrep] at htwo
  rw [Fintype.card_sigma]
  simp_rw [card_buserSarnakProjectiveConePairRepresentative hp hp2 data]
  rw [Finset.sum_const, Finset.card_univ,
    card_projectiveOctagonConeGenerator, Nat.nsmul_eq_mul]
  omega

end

end SystolicGrowth
