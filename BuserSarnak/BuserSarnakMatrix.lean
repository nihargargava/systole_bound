module

public import BuserSarnak.BuserSarnakSplit
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

@[expose] public section

namespace SystolicGrowth

noncomputable section

open Matrix

def buserSarnakSplitMatrix {p : ℕ} [NeZero p] (r s : ZMod p)
    (q : BuserSarnakQuaternionMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![q.x0 + r * q.x2 + 2 * s * q.x3,
      2 * q.x1 - 2 * s * q.x2 - 2 * r * q.x3;
     q.x1 + s * q.x2 + r * q.x3,
      q.x0 - r * q.x2 - 2 * s * q.x3]

lemma buserSarnakSplitMatrix_det {p : ℕ} [NeZero p]
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3)
    (q : BuserSarnakQuaternionMod p) :
    (buserSarnakSplitMatrix r s q).det = q.reducedNorm := by
  rw [Matrix.det_fin_two]
  simp [buserSarnakSplitMatrix, BuserSarnakQuaternionMod.reducedNorm]
  linear_combination -q.x2 ^ 2 * hrs + 2 * q.x3 ^ 2 * hrs

lemma buserSarnakSplitMatrix_mul {p : ℕ} [NeZero p]
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3)
    (q t : BuserSarnakQuaternionMod p) :
    buserSarnakSplitMatrix r s (q * t) =
      buserSarnakSplitMatrix r s q * buserSarnakSplitMatrix r s t := by
  have hrs' : r ^ 2 = 3 + 2 * s ^ 2 := by linear_combination hrs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [buserSarnakSplitMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    rw [hrs']
    ring

lemma buserSarnakSplitMatrix_one {p : ℕ} [NeZero p] (r s : ZMod p) :
    buserSarnakSplitMatrix r s 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [buserSarnakSplitMatrix]

lemma buserSarnakSplitMatrix_injective {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    Function.Injective (buserSarnakSplitMatrix r s) := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    apply six_ne_zero_zmod hp hp2 hp3
    calc
      (6 : ZMod p) = 3 * 2 := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    apply six_ne_zero_zmod hp hp2 hp3
    calc
      (6 : ZMod p) = 2 * 3 := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact mul_ne_zero htwo htwo
  intro q t h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun h (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  norm_num [buserSarnakSplitMatrix] at h00 h01 h10 h11
  have h0two : (2 : ZMod p) * q.x0 = 2 * t.x0 := by
    linear_combination h00 + h11
  have h0 : q.x0 = t.x0 := mul_left_cancel₀ htwo h0two
  have heqA2 : (2 : ZMod p) * (r * q.x2 + 2 * s * q.x3) =
      2 * (r * t.x2 + 2 * s * t.x3) := by
    linear_combination h00 - h11
  have heqA : r * q.x2 + 2 * s * q.x3 = r * t.x2 + 2 * s * t.x3 :=
    mul_left_cancel₀ htwo heqA2
  have heqB4 : (4 : ZMod p) * (s * q.x2 + r * q.x3) =
      4 * (s * t.x2 + r * t.x3) := by
    linear_combination 2 * h10 - h01
  have heqB : s * q.x2 + r * q.x3 = s * t.x2 + r * t.x3 :=
    mul_left_cancel₀ hfour heqB4
  have h2coef : (r ^ 2 - 2 * s ^ 2) * q.x2 =
      (r ^ 2 - 2 * s ^ 2) * t.x2 := by
    linear_combination r * heqA - 2 * s * heqB
  rw [hrs] at h2coef
  have h2 : q.x2 = t.x2 := mul_left_cancel₀ hthree h2coef
  have h3coef : (r ^ 2 - 2 * s ^ 2) * q.x3 =
      (r ^ 2 - 2 * s ^ 2) * t.x3 := by
    linear_combination r * heqB - s * heqA
  rw [hrs] at h3coef
  have h3 : q.x3 = t.x3 := mul_left_cancel₀ hthree h3coef
  have h1 : q.x1 = t.x1 := by
    rw [h2, h3] at h10
    linear_combination h10
  exact BuserSarnakQuaternionMod.ext h0 h1 h2 h3

def buserSarnakQuaternionModEquivProd (p : ℕ) [NeZero p] :
    BuserSarnakQuaternionMod p ≃
      ZMod p × ZMod p × ZMod p × ZMod p where
  toFun q := (q.x0, q.x1, q.x2, q.x3)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by rcases q with ⟨x0, x1, x2, x3⟩; rfl

lemma buserSarnakQuaternionMod_card_eq_matrix_card (p : ℕ) [NeZero p] :
    Fintype.card (BuserSarnakQuaternionMod p) =
      Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  rw [Fintype.card_congr (buserSarnakQuaternionModEquivProd p)]
  change Fintype.card (ZMod p × ZMod p × ZMod p × ZMod p) =
    Fintype.card (Fin 2 → Fin 2 → ZMod p)
  simp [Fintype.card_prod, ZMod.card]
  ring

lemma buserSarnakSplitMatrix_bijective {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    Function.Bijective (buserSarnakSplitMatrix r s) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨buserSarnakSplitMatrix_injective hp hp2 hp3 r s hrs,
      buserSarnakQuaternionMod_card_eq_matrix_card p⟩

def buserSarnakSplitEquiv {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    BuserSarnakQuaternionMod p ≃ Matrix (Fin 2) (Fin 2) (ZMod p) :=
  Equiv.ofBijective (buserSarnakSplitMatrix r s)
    (buserSarnakSplitMatrix_bijective hp hp2 hp3 r s hrs)

def buserSarnakNormOneEquivSL {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (r s : ZMod p) (hrs : r ^ 2 - 2 * s ^ 2 = 3) :
    BuserSarnakNormOneMod p ≃ Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  (buserSarnakSplitEquiv hp hp2 hp3 r s hrs).subtypeEquiv fun q => by
    change q.reducedNorm = 1 ↔ (buserSarnakSplitMatrix r s q).det = 1
    rw [buserSarnakSplitMatrix_det r s hrs q]

end
end SystolicGrowth
