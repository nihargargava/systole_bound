module

public import BuserSarnak.BuserSarnakSignature

@[expose] public section

namespace SystolicGrowth

noncomputable section

def squareValueSet (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.image fun x : ZMod p => x ^ 2

def affineSquareValueSet (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.image fun x : ZMod p => 3 + 2 * x ^ 2

def squareValueEncoding (p : ℕ) [NeZero p] :
    ZMod p → ↥(squareValueSet p) × Bool :=
  fun x => (⟨x ^ 2, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩, residueSignTag x)

lemma squareValueEncoding_injective (p : ℕ) [NeZero p] (hp : p.Prime) :
    Function.Injective (squareValueEncoding p) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y h
  have hsq : x ^ 2 = y ^ 2 := congrArg (fun z => z.1.1) h
  have htag : residueSignTag x = residueSignTag y := congrArg Prod.snd h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | hneg
  · exact heq
  · calc
      x = -y := hneg
      _ = y := neg_eq_self_of_signTag_neg_eq y (by simpa [hneg] using htag)

lemma squareValueSet_lower_bound (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (p + 1) / 2 ≤ (squareValueSet p).card := by
  have hcard := Fintype.card_le_of_injective (squareValueEncoding p)
    (squareValueEncoding_injective p hp)
  have hpodd := hp.odd_of_ne_two hp2
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, ZMod.card] at hcard
  obtain ⟨k, rfl⟩ := hpodd
  omega

def affineSquareValueEncoding (p : ℕ) [NeZero p] :
    ZMod p → ↥(affineSquareValueSet p) × Bool :=
  fun x => (⟨3 + 2 * x ^ 2, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩,
    residueSignTag x)

lemma affineSquareValueEncoding_injective (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Function.Injective (affineSquareValueEncoding p) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y h
  have hfirst : 3 + 2 * x ^ 2 = (3 + 2 * y ^ 2 : ZMod p) :=
    congrArg (fun z => z.1.1) h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    apply six_ne_zero_zmod hp hp2 hp3
    calc
      (6 : ZMod p) = 3 * 2 := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hsq : x ^ 2 = y ^ 2 := by
    apply mul_left_cancel₀ htwo
    linear_combination hfirst
  have htag : residueSignTag x = residueSignTag y := congrArg Prod.snd h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | hneg
  · exact heq
  · calc
      x = -y := hneg
      _ = y := neg_eq_self_of_signTag_neg_eq y (by simpa [hneg] using htag)

lemma affineSquareValueSet_lower_bound (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (p + 1) / 2 ≤ (affineSquareValueSet p).card := by
  have hcard := Fintype.card_le_of_injective (affineSquareValueEncoding p)
    (affineSquareValueEncoding_injective p hp hp2 hp3)
  have hpodd := hp.odd_of_ne_two hp2
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, ZMod.card] at hcard
  obtain ⟨k, rfl⟩ := hpodd
  omega

/-- Every good residue characteristic splits the quaternion algebra `(2,3)`. -/
theorem exists_buserSarnak_splitting_parameters (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∃ r s : ZMod p, r ^ 2 - 2 * s ^ 2 = 3 := by
  classical
  by_contra h
  push Not at h
  have hdisjoint : Disjoint (squareValueSet p) (affineSquareValueSet p) := by
    rw [Finset.disjoint_left]
    intro x hxs hxa
    rcases Finset.mem_image.mp hxs with ⟨r, -, hr⟩
    rcases Finset.mem_image.mp hxa with ⟨s, -, hs⟩
    apply h r s
    linear_combination hr - hs
  have hunion : ((squareValueSet p) ∪ (affineSquareValueSet p)).card ≤ p := by
    simpa [ZMod.card] using
      (Finset.card_le_card (Finset.subset_univ ((squareValueSet p) ∪ (affineSquareValueSet p))))
  rw [Finset.card_union_of_disjoint hdisjoint] at hunion
  have hsquare := squareValueSet_lower_bound p hp hp2
  have haffine := affineSquareValueSet_lower_bound p hp hp2 hp3
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  omega

end
end SystolicGrowth
