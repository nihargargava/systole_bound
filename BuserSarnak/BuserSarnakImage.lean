module

public import BuserSarnak.BuserSarnakFinite

@[expose] public section

namespace SystolicGrowth

noncomputable section

open Matrix

abbrev BuserSarnakReductionRange (p : ℕ) [NeZero p] :=
  (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits.range

def buserSarnakReductionImageToSL {p : ℕ} [NeZero p]
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    BuserSarnakReductionRange p →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun q := ⟨buserSarnakSplitMatrix r s q.1.1, by
    rw [buserSarnakSplitMatrix_det r s hrs]
    exact (reductionRangeToNormOne p q).2⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simpa using congrFun (congrFun (buserSarnakSplitMatrix_one r s) i) j
  map_mul' q t := by
    apply Subtype.ext
    exact buserSarnakSplitMatrix_mul r s hrs q.1.1 t.1.1

lemma buserSarnakReductionImageToSL_injective {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    Function.Injective (buserSarnakReductionImageToSL r s hrs) := by
  intro q t h
  apply Subtype.ext
  apply Units.ext
  apply buserSarnakSplitMatrix_injective hp hp2 hp3 r s hrs
  exact congrArg Subtype.val h

theorem natCard_buserSarnakReductionRange_dvd (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Nat.card (BuserSarnakReductionRange p) ∣ p * (p ^ 2 - 1) := by
  obtain ⟨r, s, hrs⟩ :=
    exists_buserSarnak_splitting_parameters p hp hp2 hp3
  let f := buserSarnakReductionImageToSL r s hrs
  have hf : Function.Injective f :=
    buserSarnakReductionImageToSL_injective hp hp2 hp3 r s hrs
  have hcardRange : Nat.card (BuserSarnakReductionRange p) =
      Nat.card f.range := by
    exact Nat.card_congr (Equiv.ofInjective (f : _ → _) hf)
  have hcardSL :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        p * (p ^ 2 - 1) := by
    rw [Nat.card_eq_fintype_card, card_specialLinearGroup_two_zmod p hp]
  rw [hcardRange, ← hcardSL]
  refine ⟨f.range.index, ?_⟩
  exact (Subgroup.card_mul_index f.range).symm

theorem principalCongruenceSubgroup23_index_eq_reductionRange_card
    (p : ℕ) [NeZero p] :
    (BuserSarnakQuaternionUnit.principalCongruenceSubgroup
      (a := 2) (b := 3) (p : ℤ)).index =
        Nat.card (BuserSarnakReductionRange p) := by
  rw [BuserSarnakQuaternionUnit.principalCongruenceSubgroup23_eq_ker_reductionUnits,
    Subgroup.index_ker]

theorem principalCongruenceSubgroup23_index_dvd_prime_cubic
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (BuserSarnakQuaternionUnit.principalCongruenceSubgroup
      (a := 2) (b := 3) (p : ℤ)).index ∣ p * (p ^ 2 - 1) := by
  rw [principalCongruenceSubgroup23_index_eq_reductionRange_card]
  exact natCard_buserSarnakReductionRange_dvd p hp hp2 hp3

def buserSarnakReductionCenter (p : ℕ) [NeZero p] :
    BuserSarnakReductionRange p :=
  ⟨(BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
      (octagonUnit .center), ⟨octagonUnit .center, rfl⟩⟩

lemma buserSarnakReductionCenter_sq (p : ℕ) [NeZero p] :
    buserSarnakReductionCenter p ^ 2 = 1 := by
  apply Subtype.ext
  change (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
      (octagonUnit .center) ^ 2 = 1
  calc
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
          (octagonUnit .center) ^ 2 =
        (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
          (octagonUnit .center ^ 2) := (map_pow _ _ 2).symm
    _ = 1 := by rw [octagon_center_sq, map_one]

lemma buserSarnakReductionCenter_ne_one (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    buserSarnakReductionCenter p ≠ 1 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    apply six_ne_zero_zmod hp hp2 hp3
    calc
      (6 : ZMod p) = 3 * 2 := by ring
      _ = 0 := by rw [hzero, mul_zero]
  intro hcenter
  have hcoord := congrArg (fun q : BuserSarnakReductionRange p => q.1.1.x0)
    hcenter
  norm_num [buserSarnakReductionCenter,
    BuserSarnakQuaternionUnit.reductionMod, octagonUnit] at hcoord
  apply htwo
  calc
    (2 : ZMod p) = 1 - (-1) := by ring
    _ = 0 := by rw [hcoord]; ring

theorem two_dvd_natCard_buserSarnakReductionRange
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    2 ∣ Nat.card (BuserSarnakReductionRange p) := by
  have horder : orderOf (buserSarnakReductionCenter p) = 2 :=
    orderOf_eq_prime (buserSarnakReductionCenter_sq p)
      (buserSarnakReductionCenter_ne_one p hp hp2 hp3)
  simpa [horder] using orderOf_dvd_natCard (buserSarnakReductionCenter p)

end
end SystolicGrowth
