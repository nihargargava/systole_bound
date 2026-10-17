module

public import BuserSarnak.BuserSarnakLevelMarking

@[expose] public section

/-!
# Central pairs in the finite Buser--Sarnak quotient

At an odd prime, multiplication by the lifted central element partitions the
finite reduction image into two-element orbits.  This module chooses one
canonical representative from each orbit and records an equivalence between
quotient states and a representative together with a Boolean side.
-/

namespace SystolicGrowth

noncomputable section

noncomputable local instance buserSarnakPairingRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakReductionRange p) :=
  Fintype.ofFinite _

/-- A deterministic numerical rank used only to orient each central pair. -/
noncomputable def buserSarnakCentralRank (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : ℕ :=
  (Fintype.equivFin (BuserSarnakReductionRange p) q).val

theorem buserSarnakCentralRank_injective (p : ℕ) [NeZero p] :
    Function.Injective (buserSarnakCentralRank p) := by
  intro q r h
  apply (Fintype.equivFin (BuserSarnakReductionRange p)).injective
  apply Fin.ext
  exact h

/-- The lower-ranked state in a central pair. -/
noncomputable def buserSarnakCentralLower (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : BuserSarnakReductionRange p :=
  if buserSarnakCentralRank p q <
      buserSarnakCentralRank p (buserSarnakCentralPartner p q) then q
  else buserSarnakCentralPartner p q

/-- The chosen lower representatives of the central two-element orbits. -/
def BuserSarnakCentralPairRepresentative (p : ℕ) [NeZero p] :=
  {q : BuserSarnakReductionRange p //
    buserSarnakCentralRank p q <
      buserSarnakCentralRank p (buserSarnakCentralPartner p q)}

noncomputable local instance buserSarnakCentralPairRepresentativeFintype
    (p : ℕ) [NeZero p] :
    Fintype (BuserSarnakCentralPairRepresentative p) :=
  Fintype.subtype
    (Finset.univ.filter fun q : BuserSarnakReductionRange p =>
      buserSarnakCentralRank p q <
        buserSarnakCentralRank p (buserSarnakCentralPartner p q))
    (by simp)

theorem buserSarnakCentralLower_lt_partner
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakReductionRange p) :
    buserSarnakCentralRank p (buserSarnakCentralLower p q) <
      buserSarnakCentralRank p
        (buserSarnakCentralPartner p (buserSarnakCentralLower p q)) := by
  rw [buserSarnakCentralLower]
  split_ifs with h
  · exact h
  · have hrankNe :
        buserSarnakCentralRank p (buserSarnakCentralPartner p q) ≠
          buserSarnakCentralRank p q := by
      intro hrank
      apply buserSarnakCentralPartner_ne p hp hp2 q
      exact buserSarnakCentralRank_injective p hrank
    have hlt :
        buserSarnakCentralRank p (buserSarnakCentralPartner p q) <
          buserSarnakCentralRank p q :=
      lt_of_le_of_ne (Nat.le_of_not_gt h) hrankNe
    simpa using hlt

/-- Boolean side of a state: `false` for the chosen lower representative and
`true` for its central partner. -/
noncomputable def buserSarnakCentralSide (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : Bool :=
  if buserSarnakCentralRank p q <
      buserSarnakCentralRank p (buserSarnakCentralPartner p q) then false
  else true

/-- Every quotient state is uniquely its central-pair representative plus a
Boolean side. -/
noncomputable def buserSarnakCentralPairEquiv
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    BuserSarnakReductionRange p ≃
      BuserSarnakCentralPairRepresentative p × Bool where
  toFun q :=
    (⟨buserSarnakCentralLower p q,
      buserSarnakCentralLower_lt_partner p hp hp2 q⟩,
      buserSarnakCentralSide p q)
  invFun qb := if qb.2 then buserSarnakCentralPartner p qb.1.1 else qb.1.1
  left_inv q := by
    by_cases h : buserSarnakCentralRank p q <
        buserSarnakCentralRank p (buserSarnakCentralPartner p q)
    · simp [buserSarnakCentralLower, buserSarnakCentralSide, h]
    · simp [buserSarnakCentralLower, buserSarnakCentralSide, h]
  right_inv qb := by
    rcases qb with ⟨⟨q, hq⟩, side⟩
    cases side
    · simp [buserSarnakCentralLower, buserSarnakCentralSide, hq]
    · have hreverse : ¬buserSarnakCentralRank p
          (buserSarnakCentralPartner p q) <
            buserSarnakCentralRank p q :=
        Nat.not_lt_of_ge hq.le
      simp [buserSarnakCentralLower, buserSarnakCentralSide,
        hreverse, buserSarnakCentralPartner_partner]

/-- Under the pair coordinates, the central action preserves the orbit
representative and flips exactly the Boolean side. -/
@[simp] theorem buserSarnakCentralPairEquiv_partner
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakReductionRange p) :
    buserSarnakCentralPairEquiv p hp hp2
        (buserSarnakCentralPartner p q) =
      ((buserSarnakCentralPairEquiv p hp hp2 q).1,
        !(buserSarnakCentralPairEquiv p hp hp2 q).2) := by
  by_cases h : buserSarnakCentralRank p q <
      buserSarnakCentralRank p (buserSarnakCentralPartner p q)
  · have hreverse : ¬buserSarnakCentralRank p
        (buserSarnakCentralPartner p q) < buserSarnakCentralRank p q :=
      Nat.not_lt_of_ge h.le
    simp [buserSarnakCentralPairEquiv, buserSarnakCentralLower,
      buserSarnakCentralSide, h, hreverse,
      buserSarnakCentralPartner_partner]
  · have hrankNe :
        buserSarnakCentralRank p (buserSarnakCentralPartner p q) ≠
          buserSarnakCentralRank p q := by
      intro hrank
      apply buserSarnakCentralPartner_ne p hp hp2 q
      exact buserSarnakCentralRank_injective p hrank
    have hreverse : buserSarnakCentralRank p
        (buserSarnakCentralPartner p q) < buserSarnakCentralRank p q :=
      lt_of_le_of_ne (Nat.le_of_not_gt h) hrankNe
    simp [buserSarnakCentralPairEquiv, buserSarnakCentralLower,
      buserSarnakCentralSide, h, hreverse,
      buserSarnakCentralPartner_partner]

/-- The number of central pairs is exactly the `halfImageIndex` used in the
genus calculation. -/
theorem card_buserSarnakCentralPairRepresentative
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (BuserSarnakCentralPairRepresentative p) =
      data.halfImageIndex := by
  have hcard := Fintype.card_congr
    (buserSarnakCentralPairEquiv p hp hp2)
  have himage := data.image_card_eq
  rw [Nat.card_eq_fintype_card] at himage
  rw [himage] at hcard
  simp only [Fintype.card_prod, Fintype.card_bool] at hcard
  omega

/-- State coordinates with the pair index identified with the exact
`halfImageIndex` appearing in the target surface genus. -/
noncomputable def buserSarnakLevelStatePairEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    BuserSarnakReductionRange p ≃ Fin data.halfImageIndex × Bool :=
  (buserSarnakCentralPairEquiv p hp hp2).trans
    (Equiv.prodCongr
      (Fintype.equivFinOfCardEq
        (card_buserSarnakCentralPairRepresentative hp hp2 data))
      (Equiv.refl Bool))

/-- In the exact finite coordinates, multiplication by the central class is
the Boolean-side flip and leaves the `Fin halfImageIndex` coordinate fixed. -/
@[simp] theorem buserSarnakLevelStatePairEquiv_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (q : BuserSarnakReductionRange p) :
    buserSarnakLevelStatePairEquiv hp hp2 data
        (buserSarnakCentralPartner p q) =
      ((buserSarnakLevelStatePairEquiv hp hp2 data q).1,
        !(buserSarnakLevelStatePairEquiv hp hp2 data q).2) := by
  simp [buserSarnakLevelStatePairEquiv]

end

end SystolicGrowth
