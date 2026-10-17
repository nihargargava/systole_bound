module

public import Core.Reduction

@[expose] public section

namespace SystolicGrowth

noncomputable section

/-! ## Arithmetic data needed by the Buser--Sarnak marking

The compactness and systole estimates are proved in `BuserSarnak`.  This file
records the arithmetic normalization forced by the octagon and bounds the
finite reduction image by a genuinely cubic set.  The remaining marking
problem is the exact presentation/index computation, not a finiteness
assumption.
-/

theorem arithmeticGenus_twelve_of_odd {p : ℕ} (hp : Odd p) :
    arithmeticGenus 12 p = (p ^ 3 - p) / 2 + 1 := by
  obtain ⟨k, hk⟩ := twenty_four_dvd_primeCubic_of_odd hp
  change 12 * (primeCubic p / 24) + 1 = primeCubic p / 2 + 1
  simp [hk]
  omega

/-- The fixed coefficient predicted by the effective octagon quotient. -/
structure FixedBuserSarnakMarking where
  marking : ∀ (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3),
    buserSarnakLevelGroup23 p ≃* SurfaceGroup (arithmeticGenus 12 p)

def FixedBuserSarnakMarking.toQuotientConstruction
    (data : FixedBuserSarnakMarking) : BuserSarnakQuotientConstruction where
  h := 12
  h_pos := by norm_num
  marking := data.marking

def BuserSarnakQuaternionMod.reducedNorm {p : ℕ} [NeZero p]
    (q : BuserSarnakQuaternionMod p) : ZMod p :=
  q.x0 ^ 2 - 2 * q.x1 ^ 2 - 3 * q.x2 ^ 2 + 6 * q.x3 ^ 2

/-- Norm-one residue quaternions.  This is the natural target of reduction. -/
def BuserSarnakNormOneMod (p : ℕ) [NeZero p] :=
  {q : BuserSarnakQuaternionMod p // q.reducedNorm = 1}

local instance (p : ℕ) [NeZero p] : Fintype (BuserSarnakNormOneMod p) :=
  Fintype.subtype (Finset.univ.filter fun q => q.reducedNorm = 1) (by simp)

/-- A deterministic choice between the two possible square roots. -/
def residueSignTag {p : ℕ} (x : ZMod p) : Bool :=
  decide (x.val ≤ (-x).val)

def normOneEncoding (p : ℕ) [NeZero p] :
    BuserSarnakNormOneMod p → (ZMod p × ZMod p × ZMod p) × Bool :=
  fun q => ((q.1.x0, q.1.x1, q.1.x2), residueSignTag q.1.x3)

lemma neg_eq_self_of_signTag_neg_eq {p : ℕ} [NeZero p] (x : ZMod p)
    (h : residueSignTag (-x) = residueSignTag x) : -x = x := by
  by_cases hle : x.val ≤ (-x).val
  · by_cases hge : (-x).val ≤ x.val
    · exact ZMod.val_injective p (le_antisymm hge hle)
    · simp [residueSignTag, hle, hge] at h
  · have hge : (-x).val ≤ x.val := le_of_not_ge hle
    simp [residueSignTag, hle, hge] at h

lemma six_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (6 : ZMod p) ≠ 0 := by
  change ((6 : ℕ) : ZMod p) ≠ 0
  intro hz
  have h6 : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp hz
  have h23 : p ∣ 2 * 3 := by norm_num at h6 ⊢; exact h6
  rcases (hp.dvd_mul).mp h23 with h2 | h3
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2 with h1 | h2'
    · exact hp.ne_one h1
    · exact hp2 h2'
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h3'
    · exact hp.ne_one h1
    · exact hp3 h3'

lemma normOneEncoding_injective (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Function.Injective (normOneEncoding p) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro q r h
  have h0 : q.1.x0 = r.1.x0 := congrArg (fun z => z.1.1) h
  have h1 : q.1.x1 = r.1.x1 := congrArg (fun z => z.1.2.1) h
  have h2 : q.1.x2 = r.1.x2 := congrArg (fun z => z.1.2.2) h
  have htag : residueSignTag q.1.x3 = residueSignTag r.1.x3 :=
    congrArg Prod.snd h
  have h6sq : (6 : ZMod p) * q.1.x3 ^ 2 = 6 * r.1.x3 ^ 2 := by
    have hq := q.2
    have hr := r.2
    simp only [BuserSarnakQuaternionMod.reducedNorm] at hq hr
    rw [h0, h1, h2] at hq
    linear_combination hq - hr
  have hsq : q.1.x3 ^ 2 = r.1.x3 ^ 2 :=
    mul_left_cancel₀ (six_ne_zero_zmod hp hp2 hp3) h6sq
  have h3 : q.1.x3 = r.1.x3 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with heq | hneg
    · exact heq
    · calc
        q.1.x3 = -r.1.x3 := hneg
        _ = r.1.x3 := neg_eq_self_of_signTag_neg_eq r.1.x3 (by simpa [hneg] using htag)
  apply Subtype.ext
  cases q with
  | mk q hq =>
    cases r with
    | mk r hr =>
      simp only at h0 h1 h2 h3 ⊢
      cases q
      cases r
      simp_all

theorem card_buserSarnakNormOneMod_le (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Fintype.card (BuserSarnakNormOneMod p) ≤ 2 * p ^ 3 := by
  have hcard := Fintype.card_le_of_injective (normOneEncoding p)
    (normOneEncoding_injective p hp hp2 hp3)
  simpa [Fintype.card_prod, Fintype.card_bool, ZMod.card, pow_succ,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

lemma reductionMod_reducedNorm_one (p : ℕ) [NeZero p]
    (q : BuserSarnakQuaternionUnit 2 3) :
    (BuserSarnakQuaternionUnit.reductionMod p q).reducedNorm = 1 := by
  simp only [BuserSarnakQuaternionMod.reducedNorm,
    BuserSarnakQuaternionUnit.reductionMod, MonoidHom.coe_mk, OneHom.coe_mk]
  have h := congrArg (fun z : ℤ => (z : ZMod p)) q.norm_one
  push_cast at h
  simpa using h

def reductionRangeToNormOne (p : ℕ) [NeZero p] :
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits.range →
      BuserSarnakNormOneMod p :=
  fun q => ⟨q.1.1, by
    rcases q.2 with ⟨x, hx⟩
    rw [← hx]
    exact reductionMod_reducedNorm_one p x⟩

lemma reductionRangeToNormOne_injective (p : ℕ) [NeZero p] :
    Function.Injective (reductionRangeToNormOne p) := by
  intro q r h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

/-- The principal congruence index is at most cubic, without strong approximation. -/
theorem principalCongruenceSubgroup23_index_le_two_mul_cube (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (BuserSarnakQuaternionUnit.principalCongruenceSubgroup
      (a := 2) (b := 3) (p : ℤ)).index ≤ 2 * p ^ 3 := by
  rw [BuserSarnakQuaternionUnit.principalCongruenceSubgroup23_eq_ker_reductionUnits,
    Subgroup.index_ker]
  letI : Fintype (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits.range :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (reductionRangeToNormOne p)
    (reductionRangeToNormOne_injective p)).trans
      (card_buserSarnakNormOneMod_le p hp hp2 hp3)

end

end SystolicGrowth
