module

public import BuserSarnak.BuserSarnakMatrix

@[expose] public section

namespace SystolicGrowth

noncomputable section

open Matrix

lemma buserSarnak_toGL_range_eq_det_ker {p : ℕ} [NeZero p] :
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod p)).range =
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    change Matrix.GeneralLinearGroup.det
      (Matrix.SpecialLinearGroup.toGL a) = 1
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.det,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.det_coe]
  · intro hg
    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
      have h := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.det] using h
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) (ZMod p)), hdet⟩, ?_⟩
    apply Units.ext
    rfl

lemma card_specialLinearGroup_two_zmod (p : ℕ) [NeZero p] (hp : p.Prime) :
    Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
      p * (p ^ 2 - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let slToGL : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
    Matrix.SpecialLinearGroup.toGL
  let glDet : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ :=
    Matrix.GeneralLinearGroup.det
  have hcardSLRange :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card slToGL.range := by
    exact Nat.card_congr
      (Equiv.ofInjective (slToGL : _ → _)
        Matrix.SpecialLinearGroup.toGL_injective)
  have hrangeKer : slToGL.range = glDet.ker :=
    buserSarnak_toGL_range_eq_det_ker
  have hcardSLKer :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card glDet.ker := by
    rw [hcardSLRange, hrangeKer]
  have hdetRange : glDet.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective glDet
      Matrix.GeneralLinearGroup.det_surjective
  have hdetIndex : glDet.ker.index = Nat.card (ZMod p)ˣ := by
    rw [Subgroup.index_ker, hdetRange]
    simp
  have hkernelProduct := Subgroup.card_mul_index glDet.ker
  rw [hdetIndex] at hkernelProduct
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hGL :
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
        (p ^ 2 - 1) * (p ^ 2 - p) := by
    simpa [Fin.prod_univ_two, ZMod.card] using
      (Matrix.card_GL_field (𝔽 := ZMod p) 2)
  have hproduct :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) =
        (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [hcardSLKer, ← hunits, ← hGL]
    exact hkernelProduct
  rw [Fintype.card_eq_nat_card]
  have hp_bound : 2 ≤ p := hp.two_le
  apply Nat.mul_right_cancel (by omega : 0 < p - 1)
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) =
        (p ^ 2 - 1) * (p ^ 2 - p) := hproduct
    _ = (p * (p ^ 2 - 1)) * (p - 1) := by
      have hfactor : p ^ 2 - p = p * (p - 1) := by
        calc
          p ^ 2 - p = p * p - p * 1 := by simp [pow_two]
          _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm
      rw [hfactor]
      ring

theorem natCard_buserSarnakNormOneMod_eq (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Nat.card (BuserSarnakNormOneMod p) = p * (p ^ 2 - 1) := by
  obtain ⟨r, s, hrs⟩ :=
    exists_buserSarnak_splitting_parameters p hp hp2 hp3
  calc
    Nat.card (BuserSarnakNormOneMod p) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      Nat.card_congr
        (buserSarnakNormOneEquivSL hp hp2 hp3 r s hrs)
    _ = Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      Nat.card_eq_fintype_card
    _ = p * (p ^ 2 - 1) := card_specialLinearGroup_two_zmod p hp

end
end SystolicGrowth
