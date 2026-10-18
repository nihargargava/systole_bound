module

public import BuserSarnak.BuserSarnakImage

@[expose] public section

namespace SystolicGrowth

noncomputable section

structure BuserSarnakCorrectionData (p : ℕ) [NeZero p] where
  halfImageIndex : ℕ
  degree : ℕ
  image_card_eq : Nat.card (BuserSarnakReductionRange p) = 2 * halfImageIndex
  full_card_eq : p * (p ^ 2 - 1) =
    Nat.card (BuserSarnakReductionRange p) * degree
  degree_pos : 0 < degree
  corrected_genus_eq : degree * halfImageIndex + 1 =
    (p * (p ^ 2 - 1)) / 2 + 1

noncomputable def buserSarnakCorrectionData (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    BuserSarnakCorrectionData p := by
  let halfImageIndex :=
    (two_dvd_natCard_buserSarnakReductionRange p hp hp2 hp3).choose
  have hhalf : Nat.card (BuserSarnakReductionRange p) = 2 * halfImageIndex := by
    simpa [halfImageIndex] using
      (two_dvd_natCard_buserSarnakReductionRange p hp hp2 hp3).choose_spec
  let degree :=
    (natCard_buserSarnakReductionRange_dvd p hp hp2 hp3).choose
  have hdegree : p * (p ^ 2 - 1) =
      Nat.card (BuserSarnakReductionRange p) * degree := by
    simpa [degree] using
      (natCard_buserSarnakReductionRange_dvd p hp hp2 hp3).choose_spec
  have hpLower : 2 ≤ p := hp.two_le
  have hsquare : 1 < p ^ 2 := by nlinarith
  have hfullPos : 0 < p * (p ^ 2 - 1) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hsquare)
  have hdegreePos : 0 < degree := by
    by_contra hnonpos
    have hzero : degree = 0 := Nat.eq_zero_of_not_pos hnonpos
    rw [hzero, mul_zero] at hdegree
    omega
  refine ⟨halfImageIndex, degree, hhalf, hdegree, hdegreePos, ?_⟩
  rw [hdegree, hhalf]
  rw [show 2 * halfImageIndex * degree = 2 * (halfImageIndex * degree) by ring]
  rw [Nat.mul_div_cancel_left (halfImageIndex * degree) (by norm_num : 0 < 2)]
  ring
end
end SystolicGrowth
