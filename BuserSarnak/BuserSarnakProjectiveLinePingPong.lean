module

public import BuserSarnak.BuserSarnakProjectiveCenter
public import Mathlib.LinearAlgebra.Projectivization.Action

@[expose] public section

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

/-!
# Projective-line ping-pong for the octagon HNN base

The HNN base is a free product of one infinite cyclic handle factor and four
order-two cone factors.  This file constructs five disjoint regions in the
real projective line and verifies the explicit quaternion matrices satisfy
Mathlib's coproduct ping-pong hypotheses.  Consequently the PGL realization
is faithful on the entire HNN base.
-/

/-- The real projective line on which the explicit quaternion matrices act. -/
abbrev OctagonProjectiveLine := ℙ ℝ (Fin 2 → ℝ)

def projectiveQuadraticNegativeSet (Q : (Fin 2 → ℝ) → ℝ) : Set OctagonProjectiveLine :=
  {p | Q p.rep < 0}

lemma mem_projectiveQuadraticNegativeSet_mk_iff (Q : (Fin 2 → ℝ) → ℝ)
    (hQ : ∀ (t : ℝ) (v : Fin 2 → ℝ), Q (t • v) = t ^ 2 * Q v)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ projectiveQuadraticNegativeSet Q ↔ Q v < 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  change Q (Projectivization.mk ℝ v hv).rep < 0 ↔ Q v < 0
  rw [← ha]
  change Q ((a : ℝ) • v) < 0 ↔ Q v < 0
  rw [hQ]
  have ha0 : (a : ℝ) ≠ 0 := Units.ne_zero a
  have hapos : 0 < (a : ℝ) ^ 2 := sq_pos_of_ne_zero ha0
  constructor <;> intro h <;> nlinarith

def projectiveIntervalQuadratic (l u : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  (v 0 - l * v 1) * (v 0 - u * v 1)

lemma projectiveIntervalQuadratic_smul (l u t : ℝ) (v : Fin 2 → ℝ) :
    projectiveIntervalQuadratic l u (t • v) = t ^ 2 * projectiveIntervalQuadratic l u v := by
  simp [projectiveIntervalQuadratic, Pi.smul_apply, smul_eq_mul]
  ring

def projectiveIntervalSet (l u : ℝ) : Set OctagonProjectiveLine :=
  projectiveQuadraticNegativeSet (projectiveIntervalQuadratic l u)

@[simp] lemma mem_projectiveIntervalSet_mk_iff (l u : ℝ)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ projectiveIntervalSet l u ↔
      projectiveIntervalQuadratic l u v < 0 :=
  mem_projectiveQuadraticNegativeSet_mk_iff _ (projectiveIntervalQuadratic_smul l u) v hv

def octagonHandleInnerQuadratic (v : Fin 2 → ℝ) : ℝ := 16 * (v 0) ^ 2 - (v 1) ^ 2
def octagonHandleOuterQuadratic (v : Fin 2 → ℝ) : ℝ := 16 * (v 1) ^ 2 - (v 0) ^ 2

lemma octagonHandleInnerQuadratic_smul (t : ℝ) (v : Fin 2 → ℝ) :
    octagonHandleInnerQuadratic (t • v) = t ^ 2 * octagonHandleInnerQuadratic v := by
  simp [octagonHandleInnerQuadratic, Pi.smul_apply, smul_eq_mul]
  ring

lemma octagonHandleOuterQuadratic_smul (t : ℝ) (v : Fin 2 → ℝ) :
    octagonHandleOuterQuadratic (t • v) = t ^ 2 * octagonHandleOuterQuadratic v := by
  simp [octagonHandleOuterQuadratic, Pi.smul_apply, smul_eq_mul]
  ring

def octagonHandleProjectiveLineSet : Set OctagonProjectiveLine := projectiveQuadraticNegativeSet octagonHandleInnerQuadratic ∪ projectiveQuadraticNegativeSet octagonHandleOuterQuadratic
def octagonCone1ProjectiveLineSet : Set OctagonProjectiveLine := projectiveIntervalSet (-1) (-1 / 4)
def octagonCone2ProjectiveLineSet : Set OctagonProjectiveLine := projectiveIntervalSet (1 / 4) 1
def octagonCone3ProjectiveLineSet : Set OctagonProjectiveLine := projectiveIntervalSet 1 4
def octagonCone4ProjectiveLineSet : Set OctagonProjectiveLine := projectiveIntervalSet (-4) (-1)

/-- The five projective-line regions used for free-product ping-pong. -/
def octagonBasePingPongSet : OctagonBaseFactor → Set OctagonProjectiveLine
  | .handle => octagonHandleProjectiveLineSet
  | .cone1 => octagonCone1ProjectiveLineSet
  | .cone2 => octagonCone2ProjectiveLineSet
  | .cone3 => octagonCone3ProjectiveLineSet
  | .cone4 => octagonCone4ProjectiveLineSet

def octagonBasePingPongQuadraticProp : OctagonBaseFactor → (Fin 2 → ℝ) → Prop
  | .handle => fun v => octagonHandleInnerQuadratic v < 0 ∨ octagonHandleOuterQuadratic v < 0
  | .cone1 => fun v => projectiveIntervalQuadratic (-1) (-1 / 4) v < 0
  | .cone2 => fun v => projectiveIntervalQuadratic (1 / 4) 1 v < 0
  | .cone3 => fun v => projectiveIntervalQuadratic 1 4 v < 0
  | .cone4 => fun v => projectiveIntervalQuadratic (-4) (-1) v < 0

lemma mem_octagonHandleProjectiveLineSet_mk_iff (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ octagonHandleProjectiveLineSet ↔
      octagonHandleInnerQuadratic v < 0 ∨ octagonHandleOuterQuadratic v < 0 := by
  simp only [octagonHandleProjectiveLineSet, Set.mem_union]
  rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleInnerQuadratic_smul,
    mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleOuterQuadratic_smul]

@[simp] lemma mem_octagonBasePingPongSet_mk_iff (i : OctagonBaseFactor)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ octagonBasePingPongSet i ↔ octagonBasePingPongQuadraticProp i v := by
  cases i with
  | handle => exact mem_octagonHandleProjectiveLineSet_mk_iff v hv
  | cone1 => exact mem_projectiveIntervalSet_mk_iff _ _ v hv
  | cone2 => exact mem_projectiveIntervalSet_mk_iff _ _ v hv
  | cone3 => exact mem_projectiveIntervalSet_mk_iff _ _ v hv
  | cone4 => exact mem_projectiveIntervalSet_mk_iff _ _ v hv

/-- Every projective-line ping-pong region is nonempty. -/
lemma octagonBasePingPongSet_nonempty (i : OctagonBaseFactor) :
    (octagonBasePingPongSet i).Nonempty := by
  cases i with
  | handle =>
      let v : Fin 2 → ℝ := ![0, 1]
      refine ⟨Projectivization.mk ℝ v (by simp [v]), ?_⟩
      change Projectivization.mk ℝ v _ ∈ octagonHandleProjectiveLineSet
      rw [mem_octagonHandleProjectiveLineSet_mk_iff]
      left
      norm_num [octagonHandleInnerQuadratic, v]
  | cone1 =>
      let v : Fin 2 → ℝ := ![-1 / 2, 1]
      refine ⟨Projectivization.mk ℝ v (by simp [v]), ?_⟩
      change Projectivization.mk ℝ v _ ∈ octagonCone1ProjectiveLineSet
      change Projectivization.mk ℝ v _ ∈ projectiveIntervalSet (-1) (-1 / 4)
      rw [mem_projectiveIntervalSet_mk_iff]
      norm_num [octagonCone1ProjectiveLineSet, octagonBasePingPongSet, projectiveIntervalQuadratic, v]
  | cone2 =>
      let v : Fin 2 → ℝ := ![1 / 2, 1]
      refine ⟨Projectivization.mk ℝ v (by simp [v]), ?_⟩
      change Projectivization.mk ℝ v _ ∈ octagonCone2ProjectiveLineSet
      change Projectivization.mk ℝ v _ ∈ projectiveIntervalSet (1 / 4) 1
      rw [mem_projectiveIntervalSet_mk_iff]
      norm_num [octagonCone2ProjectiveLineSet, octagonBasePingPongSet, projectiveIntervalQuadratic, v]
  | cone3 =>
      let v : Fin 2 → ℝ := ![2, 1]
      refine ⟨Projectivization.mk ℝ v (by simp [v]), ?_⟩
      change Projectivization.mk ℝ v _ ∈ octagonCone3ProjectiveLineSet
      change Projectivization.mk ℝ v _ ∈ projectiveIntervalSet 1 4
      rw [mem_projectiveIntervalSet_mk_iff]
      norm_num [octagonCone3ProjectiveLineSet, octagonBasePingPongSet, projectiveIntervalQuadratic, v]
  | cone4 =>
      let v : Fin 2 → ℝ := ![-2, 1]
      refine ⟨Projectivization.mk ℝ v (by simp [v]), ?_⟩
      change Projectivization.mk ℝ v _ ∈ octagonCone4ProjectiveLineSet
      change Projectivization.mk ℝ v _ ∈ projectiveIntervalSet (-4) (-1)
      rw [mem_projectiveIntervalSet_mk_iff]
      norm_num [octagonCone4ProjectiveLineSet, octagonBasePingPongSet, projectiveIntervalQuadratic, v]

/-- Distinct free-product factors have disjoint ping-pong regions. -/
lemma octagonBasePingPongSet_pairwise_disjoint :
    Pairwise fun i j => Disjoint (octagonBasePingPongSet i) (octagonBasePingPongSet j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro p hip hjp
  induction p using Projectivization.ind with
  | _ v hv =>
      rw [mem_octagonBasePingPongSet_mk_iff] at hip hjp
      cases i <;> cases j <;>
        simp_all [octagonBasePingPongQuadraticProp, octagonHandleInnerQuadratic, octagonHandleOuterQuadratic, projectiveIntervalQuadratic]
      all_goals try nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      all_goals first
        | (rcases hip with hip | hip <;>
            nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)])
        | (rcases hjp with hjp | hjp <;>
            nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)])

abbrev quaternionGL23 (q : BSUnit23) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.toGL
    (BuserSarnakQuaternionUnit.toSLHom
      (a := 2) (b := 3) (by norm_num) (by norm_num) q)

@[simp] lemma toPGL23_smul_projective_mk (q : BSUnit23)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    BuserSarnakQuaternionUnit.toPGL23 q •
        Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ (quaternionGL23 q • v)
        (smul_ne_zero_iff_ne (quaternionGL23 q) |>.2 hv) := by
  rfl

lemma octagonBTrueFalse_maps_cone2ProjectiveLineSet :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23
          (octagonUnit (.B true false)) • p)
      octagonCone2ProjectiveLineSet octagonCone1ProjectiveLineSet := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      change Projectivization.mk ℝ _ _ ∈ octagonBasePingPongSet .cone1
      rw [mem_octagonBasePingPongSet_mk_iff]
      change Projectivization.mk ℝ v hv ∈ octagonBasePingPongSet .cone2 at hp
      rw [mem_octagonBasePingPongSet_mk_iff] at hp
      simp only [octagonBasePingPongQuadraticProp, projectiveIntervalQuadratic] at hp ⊢
      simp [quaternionGL23, BuserSarnakQuaternionUnit.toSLHom,
        BuserSarnakQuaternionUnit.toSL, BuserSarnakQuaternionUnit.matrix,
        buserSarnakMatrix, octagonUnit, Matrix.SpecialLinearGroup.toGL,
        Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec,
        Matrix.vecHead, Matrix.vecTail,
        octagonSign] at ⊢
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      have hs23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have ha_lo : (707 / 500 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have ha_hi : Real.sqrt 2 < (283 / 200 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hb_lo : (433 / 250 : ℝ) < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hb_hi : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hc_lo : (2449 / 1000 : ℝ) < Real.sqrt 6 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hc_hi : Real.sqrt 6 < (49 / 20 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      let Acoef : ℝ := -5 / 4 * (Real.sqrt 2 * Real.sqrt 3) +
        3 / 2 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 13 / 4
      let Bcoef : ℝ := -3 / 2 * (Real.sqrt 2 * Real.sqrt 3) +
        5 * Real.sqrt 3 - 5
      let Ccoef : ℝ := 5 / 4 * (Real.sqrt 2 * Real.sqrt 3) -
        6 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 37 / 4
      have hA : Acoef < -2 := by
        dsimp [Acoef]
        rw [hs23]
        linarith
      have hB_lo : (-3 / 200 : ℝ) < Bcoef := by
        dsimp [Bcoef]
        rw [hs23]
        linarith
      have hB_hi : Bcoef < 0 := by
        dsimp [Bcoef]
        rw [hs23]
        linarith
      have hC : Ccoef < -1 / 2 := by
        dsimp [Ccoef]
        rw [hs23]
        linarith
      have hAx : Acoef * (v 0) ^ 2 ≤ -2 * (v 0) ^ 2 :=
        mul_le_mul_of_nonneg_right hA.le (sq_nonneg _)
      have hCy : Ccoef * (v 1) ^ 2 ≤ (-1 / 2) * (v 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)
      have hR : Acoef * (v 0) ^ 2 + Bcoef * v 0 * v 1 +
          Ccoef * (v 1) ^ 2 ≤ 0 := by
        by_cases hxy : 0 ≤ v 0 * v 1
        · have hBxy : Bcoef * (v 0 * v 1) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hB_hi.le hxy
          nlinarith
        · have hxy' : v 0 * v 1 ≤ 0 := le_of_not_ge hxy
          have hBxy : Bcoef * (v 0 * v 1) ≤
              (-3 / 200 : ℝ) * (v 0 * v 1) :=
            mul_le_mul_of_nonpos_right hB_lo.le hxy'
          nlinarith [sq_nonneg (v 0 + v 1)]
      have hout :
          (Real.sqrt 2 * v 0 + Real.sqrt 3 * (-1 + Real.sqrt 2) * v 1 -
              (Real.sqrt 2 * v 1 +
                -(Real.sqrt 3 * (-1 - Real.sqrt 2) * v 0))) *
            (Real.sqrt 2 * v 0 +
                Real.sqrt 3 * (-1 + Real.sqrt 2) * v 1 -
              (-1 / 4 : ℝ) *
                (Real.sqrt 3 * (-1 - Real.sqrt 2) * v 0 +
                  -(Real.sqrt 2 * v 1))) =
          (v 0 - (1 / 4 : ℝ) * v 1) * (v 0 - v 1) +
            Acoef * (v 0) ^ 2 + Bcoef * v 0 * v 1 +
              Ccoef * (v 1) ^ 2 := by
        dsimp [Acoef, Bcoef, Ccoef]
        ring_nf
        rw [hs2, hs3]
        ring
      rw [hout]
      nlinarith

lemma small_quadratic_neg_of_bounds {A B C x y : ℝ}
    (hv : x ≠ 0 ∨ y ≠ 0)
    (hA : A < -1 / 50) (hB_lo : -3 / 200 < B)
    (hB_hi : B < 3 / 200) (hC : C < -3 / 1000) :
    A * x ^ 2 + B * x * y + C * y ^ 2 < 0 := by
  have hdiag : A * x ^ 2 + C * y ^ 2 <
      (-1 / 50 : ℝ) * x ^ 2 + (-3 / 1000 : ℝ) * y ^ 2 := by
    rcases hv with hx | hy
    · have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hAx := mul_lt_mul_of_pos_right hA hxpos
      have hCy := mul_le_mul_of_nonneg_right hC.le (sq_nonneg y)
      nlinarith
    · have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hAx := mul_le_mul_of_nonneg_right hA.le (sq_nonneg x)
      have hCy := mul_lt_mul_of_pos_right hC hypos
      nlinarith
  by_cases hxy : 0 ≤ x * y
  · have hcross : B * (x * y) ≤ (3 / 200 : ℝ) * (x * y) :=
      mul_le_mul_of_nonneg_right hB_hi.le hxy
    nlinarith [sq_nonneg (5 * x - 2 * y)]
  · have hxy' : x * y ≤ 0 := le_of_not_ge hxy
    have hcross : B * (x * y) ≤ (-3 / 200 : ℝ) * (x * y) :=
      mul_le_mul_of_nonpos_right hB_lo.le hxy'
    nlinarith [sq_nonneg (5 * x + 2 * y)]

lemma large_quadratic_neg_of_bounds {A B C x y : ℝ}
    (hv : x ≠ 0 ∨ y ≠ 0)
    (hA : A < -7 / 500) (hB_lo : -7 / 125 < B)
    (hB_hi : B < 7 / 125) (hC : C < -2 / 25) :
    A * x ^ 2 + B * x * y + C * y ^ 2 < 0 := by
  have hdiag : A * x ^ 2 + C * y ^ 2 <
      (-7 / 500 : ℝ) * x ^ 2 + (-2 / 25 : ℝ) * y ^ 2 := by
    rcases hv with hx | hy
    · have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hAx := mul_lt_mul_of_pos_right hA hxpos
      have hCy := mul_le_mul_of_nonneg_right hC.le (sq_nonneg y)
      nlinarith
    · have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hAx := mul_le_mul_of_nonneg_right hA.le (sq_nonneg x)
      have hCy := mul_lt_mul_of_pos_right hC hypos
      nlinarith
  by_cases hxy : 0 ≤ x * y
  · have hcross : B * (x * y) ≤ (7 / 125 : ℝ) * (x * y) :=
      mul_le_mul_of_nonneg_right hB_hi.le hxy
    nlinarith [sq_nonneg (x - 2 * y)]
  · have hxy' : x * y ≤ 0 := le_of_not_ge hxy
    have hcross : B * (x * y) ≤ (-7 / 125 : ℝ) * (x * y) :=
      mul_le_mul_of_nonpos_right hB_lo.le hxy'
    nlinarith [sq_nonneg (x + 2 * y)]

def octagonBBaseFactor : Bool → Bool → OctagonBaseFactor
  | true, false => .cone1
  | false, false => .cone2
  | false, true => .cone3
  | true, true => .cone4

/-- Each projective cone involution sends the complement of its region
strictly into that region. -/
lemma octagonB_maps_compl_basePingPongSet (s t : Bool) :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.B s t)) • p)
      (octagonBasePingPongSet (octagonBBaseFactor s t))ᶜ
      (octagonBasePingPongSet (octagonBBaseFactor s t)) := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      rw [mem_octagonBasePingPongSet_mk_iff]
      have hp' : ¬Projectivization.mk ℝ v hv ∈
          octagonBasePingPongSet (octagonBBaseFactor s t) := hp
      rw [mem_octagonBasePingPongSet_mk_iff] at hp'
      have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_cases h0 : v 0 = 0
        · right
          intro h1
          apply hv
          funext i
          fin_cases i <;> assumption
        · exact Or.inl h0
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hs23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have ha_lo : (141421 / 100000 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have ha_hi : Real.sqrt 2 < (141422 / 100000 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hb_lo : (173205 / 100000 : ℝ) < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hb_hi : Real.sqrt 3 < (173206 / 100000 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hc_lo : (244948 / 100000 : ℝ) < Real.sqrt 6 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hc_hi : Real.sqrt 6 < (244949 / 100000 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      cases s <;> cases t
      · change projectiveIntervalQuadratic (1 / 4) 1
            (quaternionGL23 (octagonUnit (.B false false)) • v) < 0
        change ¬projectiveIntervalQuadratic (1 / 4) 1 v < 0 at hp'
        have hq : 0 ≤ projectiveIntervalQuadratic (1 / 4) 1 v := le_of_not_gt hp'
        let A : ℝ := -5 / 4 * (Real.sqrt 2 * Real.sqrt 3) +
          3 / 2 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 21 / 4
        let B : ℝ := 3 / 2 * (Real.sqrt 2 * Real.sqrt 3) -
          5 * Real.sqrt 3 + 5
        let C : ℝ := 5 / 4 * (Real.sqrt 2 * Real.sqrt 3) -
          6 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 39 / 4
        have hA : A < -1 / 50 := by
          dsimp [A]
          rw [hs23]
          linarith
        have hB_lo : (-3 / 200 : ℝ) < B := by
          dsimp [B]
          rw [hs23]
          linarith
        have hB_hi : B < 3 / 200 := by
          dsimp [B]
          rw [hs23]
          linarith
        have hC : C < -3 / 1000 := by
          dsimp [C]
          rw [hs23]
          linarith
        have hR := small_quadratic_neg_of_bounds hv' hA hB_lo hB_hi hC
        have hout : projectiveIntervalQuadratic (1 / 4) 1
              (quaternionGL23 (octagonUnit (.B false false)) • v) =
            -projectiveIntervalQuadratic (1 / 4) 1 v +
              A * (v 0) ^ 2 + B * v 0 * v 1 + C * (v 1) ^ 2 := by
          simp [projectiveIntervalQuadratic, quaternionGL23,
            BuserSarnakQuaternionUnit.toSLHom,
            BuserSarnakQuaternionUnit.toSL,
            BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
            Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
            Matrix.vecTail, octagonSign]
          dsimp [A, B, C]
          ring_nf
          rw [hs2, hs3]
          ring
        rw [hout]
        nlinarith

      · change projectiveIntervalQuadratic 1 4
            (quaternionGL23 (octagonUnit (.B false true)) • v) < 0
        change ¬projectiveIntervalQuadratic 1 4 v < 0 at hp'
        have hq : 0 ≤ projectiveIntervalQuadratic 1 4 v := le_of_not_gt hp'
        let A : ℝ := 5 * (Real.sqrt 2 * Real.sqrt 3) -
          24 * Real.sqrt 2 - 10 * Real.sqrt 3 + 39
        let B : ℝ := 6 * (Real.sqrt 2 * Real.sqrt 3) -
          20 * Real.sqrt 3 + 20
        let C : ℝ := -5 * (Real.sqrt 2 * Real.sqrt 3) +
          6 * Real.sqrt 2 - 10 * Real.sqrt 3 + 21
        have hA : A < -7 / 500 := by
          dsimp [A]
          rw [hs23]
          linarith
        have hB_lo : (-7 / 125 : ℝ) < B := by
          dsimp [B]
          rw [hs23]
          linarith
        have hB_hi : B < 7 / 125 := by
          dsimp [B]
          rw [hs23]
          linarith
        have hC : C < -2 / 25 := by
          dsimp [C]
          rw [hs23]
          linarith
        have hR := large_quadratic_neg_of_bounds hv' hA hB_lo hB_hi hC
        have hout : projectiveIntervalQuadratic 1 4
              (quaternionGL23 (octagonUnit (.B false true)) • v) =
            -projectiveIntervalQuadratic 1 4 v +
              A * (v 0) ^ 2 + B * v 0 * v 1 + C * (v 1) ^ 2 := by
          simp [projectiveIntervalQuadratic, quaternionGL23,
            BuserSarnakQuaternionUnit.toSLHom,
            BuserSarnakQuaternionUnit.toSL,
            BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
            Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
            Matrix.vecTail, octagonSign]
          dsimp [A, B, C]
          ring_nf
          rw [hs2, hs3]
          ring
        rw [hout]
        nlinarith
      · change projectiveIntervalQuadratic (-1) (-1 / 4)
            (quaternionGL23 (octagonUnit (.B true false)) • v) < 0
        change ¬projectiveIntervalQuadratic (-1) (-1 / 4) v < 0 at hp'
        have hq : 0 ≤ projectiveIntervalQuadratic (-1) (-1 / 4) v := le_of_not_gt hp'
        let A : ℝ := -5 / 4 * (Real.sqrt 2 * Real.sqrt 3) +
          3 / 2 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 21 / 4
        let B : ℝ := -3 / 2 * (Real.sqrt 2 * Real.sqrt 3) +
          5 * Real.sqrt 3 - 5
        let C : ℝ := 5 / 4 * (Real.sqrt 2 * Real.sqrt 3) -
          6 * Real.sqrt 2 - 5 / 2 * Real.sqrt 3 + 39 / 4
        have hA : A < -1 / 50 := by
          dsimp [A]
          rw [hs23]
          linarith
        have hB_lo : (-3 / 200 : ℝ) < B := by
          dsimp [B]
          rw [hs23]
          linarith
        have hB_hi : B < 3 / 200 := by
          dsimp [B]
          rw [hs23]
          linarith
        have hC : C < -3 / 1000 := by
          dsimp [C]
          rw [hs23]
          linarith
        have hR := small_quadratic_neg_of_bounds hv' hA hB_lo hB_hi hC
        have hout : projectiveIntervalQuadratic (-1) (-1 / 4)
              (quaternionGL23 (octagonUnit (.B true false)) • v) =
            -projectiveIntervalQuadratic (-1) (-1 / 4) v +
              A * (v 0) ^ 2 + B * v 0 * v 1 + C * (v 1) ^ 2 := by
          simp [projectiveIntervalQuadratic, quaternionGL23,
            BuserSarnakQuaternionUnit.toSLHom,
            BuserSarnakQuaternionUnit.toSL,
            BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
            Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
            Matrix.vecTail, octagonSign]
          dsimp [A, B, C]
          ring_nf
          rw [hs2, hs3]
          ring
        rw [hout]
        nlinarith
      · change projectiveIntervalQuadratic (-4) (-1)
            (quaternionGL23 (octagonUnit (.B true true)) • v) < 0
        change ¬projectiveIntervalQuadratic (-4) (-1) v < 0 at hp'
        have hq : 0 ≤ projectiveIntervalQuadratic (-4) (-1) v := le_of_not_gt hp'
        let A : ℝ := 5 * (Real.sqrt 2 * Real.sqrt 3) -
          24 * Real.sqrt 2 - 10 * Real.sqrt 3 + 39
        let B : ℝ := -6 * (Real.sqrt 2 * Real.sqrt 3) +
          20 * Real.sqrt 3 - 20
        let C : ℝ := -5 * (Real.sqrt 2 * Real.sqrt 3) +
          6 * Real.sqrt 2 - 10 * Real.sqrt 3 + 21
        have hA : A < -7 / 500 := by
          dsimp [A]
          rw [hs23]
          linarith
        have hB_lo : (-7 / 125 : ℝ) < B := by
          dsimp [B]
          rw [hs23]
          linarith
        have hB_hi : B < 7 / 125 := by
          dsimp [B]
          rw [hs23]
          linarith
        have hC : C < -2 / 25 := by
          dsimp [C]
          rw [hs23]
          linarith
        have hR := large_quadratic_neg_of_bounds hv' hA hB_lo hB_hi hC
        have hout : projectiveIntervalQuadratic (-4) (-1)
              (quaternionGL23 (octagonUnit (.B true true)) • v) =
            -projectiveIntervalQuadratic (-4) (-1) v +
              A * (v 0) ^ 2 + B * v 0 * v 1 + C * (v 1) ^ 2 := by
          simp [projectiveIntervalQuadratic, quaternionGL23,
            BuserSarnakQuaternionUnit.toSLHom,
            BuserSarnakQuaternionUnit.toSL,
            BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
            Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
            Matrix.vecTail, octagonSign]
          dsimp [A, B, C]
          ring_nf
          rw [hs2, hs3]
          ring
        rw [hout]
        nlinarith

lemma octagonA_true_maps_compl_handleSet :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.A true)) • p)
      octagonHandleProjectiveLineSetᶜ (projectiveQuadraticNegativeSet octagonHandleOuterQuadratic) := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleOuterQuadratic_smul]
      have hp' : ¬Projectivization.mk ℝ v hv ∈ octagonHandleProjectiveLineSet := hp
      rw [mem_octagonHandleProjectiveLineSet_mk_iff] at hp'
      push Not at hp'
      have hx : v 0 ≠ 0 := by
        intro hx
        have hy : v 1 = 0 := by
          dsimp [octagonHandleInnerQuadratic] at hp'
          rw [hx] at hp'
          norm_num at hp'
          nlinarith [sq_nonneg (v 1)]
        apply hv
        funext i
        fin_cases i <;> assumption
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2lo : (707 / 500 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      simp [octagonHandleOuterQuadratic, quaternionGL23,
        BuserSarnakQuaternionUnit.toSLHom,
        BuserSarnakQuaternionUnit.toSL,
        BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
        octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
        Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
        Matrix.vecTail, octagonSign]
      ring_nf
      rw [hs2]
      dsimp [octagonHandleInnerQuadratic] at hp'
      have hxpos : 0 < (v 0) ^ 2 := sq_pos_of_ne_zero hx
      nlinarith

lemma octagonA_false_maps_compl_handleSet :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.A false)) • p)
      octagonHandleProjectiveLineSetᶜ (projectiveQuadraticNegativeSet octagonHandleInnerQuadratic) := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleInnerQuadratic_smul]
      have hp' : ¬Projectivization.mk ℝ v hv ∈ octagonHandleProjectiveLineSet := hp
      rw [mem_octagonHandleProjectiveLineSet_mk_iff] at hp'
      push Not at hp'
      have hy : v 1 ≠ 0 := by
        intro hy
        have hx : v 0 = 0 := by
          dsimp [octagonHandleOuterQuadratic] at hp'
          rw [hy] at hp'
          norm_num at hp'
          nlinarith [sq_nonneg (v 0)]
        apply hv
        funext i
        fin_cases i <;> assumption
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2lo : (707 / 500 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      simp [octagonHandleInnerQuadratic, quaternionGL23,
        BuserSarnakQuaternionUnit.toSLHom,
        BuserSarnakQuaternionUnit.toSL,
        BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
        octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
        Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
        Matrix.vecTail, octagonSign]
      ring_nf
      rw [hs2]
      dsimp [octagonHandleOuterQuadratic] at hp'
      have hypos : 0 < (v 1) ^ 2 := sq_pos_of_ne_zero hy
      nlinarith

lemma octagonA_true_maps_outerSet :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.A true)) • p)
      (projectiveQuadraticNegativeSet octagonHandleOuterQuadratic) (projectiveQuadraticNegativeSet octagonHandleOuterQuadratic) := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleOuterQuadratic_smul]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleOuterQuadratic_smul] at hp
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2lo : (707 / 500 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      simp [octagonHandleOuterQuadratic, quaternionGL23,
        BuserSarnakQuaternionUnit.toSLHom,
        BuserSarnakQuaternionUnit.toSL,
        BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
        octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
        Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
        Matrix.vecTail, octagonSign]
      ring_nf
      rw [hs2]
      dsimp [octagonHandleOuterQuadratic] at hp
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma octagonA_false_maps_innerSet :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.A false)) • p)
      (projectiveQuadraticNegativeSet octagonHandleInnerQuadratic) (projectiveQuadraticNegativeSet octagonHandleInnerQuadratic) := by
  intro p hp
  induction p using Projectivization.ind with
  | _ v hv =>
      dsimp only
      rw [toPGL23_smul_projective_mk]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleInnerQuadratic_smul]
      rw [mem_projectiveQuadraticNegativeSet_mk_iff _ octagonHandleInnerQuadratic_smul] at hp
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2lo : (707 / 500 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      simp [octagonHandleInnerQuadratic, quaternionGL23,
        BuserSarnakQuaternionUnit.toSLHom,
        BuserSarnakQuaternionUnit.toSL,
        BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
        octagonUnit, Matrix.SpecialLinearGroup.toGL, Units.smul_def,
        Matrix.smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead,
        Matrix.vecTail, octagonSign]
      ring_nf
      rw [hs2]
      dsimp [octagonHandleInnerQuadratic] at hp
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma octagonA_pos_pow_maps_compl_handleSet (k : ℕ) :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        (BuserSarnakQuaternionUnit.toPGL23
          (octagonUnit (.A true))) ^ (k + 1) • p)
      octagonHandleProjectiveLineSetᶜ (projectiveQuadraticNegativeSet octagonHandleOuterQuadratic) := by
  induction k with
  | zero => simpa using octagonA_true_maps_compl_handleSet
  | succ k ih =>
      intro p hp
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ']
      dsimp only
      rw [mul_smul]
      exact octagonA_true_maps_outerSet (ih hp)

lemma octagonA_neg_pow_maps_compl_handleSet (k : ℕ) :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        (BuserSarnakQuaternionUnit.toPGL23
          (octagonUnit (.A false))) ^ (k + 1) • p)
      octagonHandleProjectiveLineSetᶜ (projectiveQuadraticNegativeSet octagonHandleInnerQuadratic) := by
  induction k with
  | zero => simpa using octagonA_false_maps_compl_handleSet
  | succ k ih =>
      intro p hp
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ']
      dsimp only
      rw [mul_smul]
      exact octagonA_false_maps_innerSet (ih hp)

/-- Every nonzero handle power sends the complement of the two-sided handle
region into the handle region. -/
lemma octagonA_zpow_maps_compl_handleSet (n : ℤ) (hn : n ≠ 0) :
    Set.MapsTo
      (fun p : OctagonProjectiveLine =>
        (BuserSarnakQuaternionUnit.toPGL23
          (octagonUnit (.A true))) ^ n • p)
      octagonHandleProjectiveLineSetᶜ octagonHandleProjectiveLineSet := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ k =>
          intro p hp
          have hout := octagonA_pos_pow_maps_compl_handleSet k hp
          change _ ∈ octagonHandleProjectiveLineSet
          exact Or.inr hout
  | negSucc k =>
      intro p hp
      have hinv :
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.A true)))⁻¹ =
          BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.A false)) := by
        rw [← map_inv, ← octagon_A_false_eq_inv]
      rw [zpow_negSucc]
      dsimp only
      rw [← inv_pow, hinv]
      have hinner := octagonA_neg_pow_maps_compl_handleSet k hp
      change _ ∈ octagonHandleProjectiveLineSet
      exact Or.inl hinner

lemma zpow_eq_self_of_orderOf_eq_two {G : Type*} [Group G]
    {g : G} (hg : orderOf g = 2) (n : ℤ) (hne : g ^ n ≠ 1) :
    g ^ n = g := by
  have hsq : g ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one g
    simpa [hg] using hpow
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · exfalso
    apply hne
    rw [hk, zpow_mul]
    norm_num only [zpow_ofNat]
    rw [hsq, one_zpow]
  · rw [hk, zpow_add_one, zpow_mul]
    norm_num only [zpow_ofNat]
    rw [hsq, one_zpow, one_mul]

/-- The five factor restrictions satisfy the action hypothesis of the
coproduct ping-pong lemma. -/
lemma octagonBaseFactor_pingPong :
    Pairwise fun i j => ∀ h : OctagonBaseFactorGroup i, h ≠ 1 →
      Set.MapsTo
        (fun p : OctagonProjectiveLine =>
          (octagonBaseToPGL23.comp (octagonBaseFactorInclusion i)) h • p)
        (octagonBasePingPongSet j) (octagonBasePingPongSet i) := by
  intro i j hij h hh p hp
  have hpcompl : p ∈ (octagonBasePingPongSet i)ᶜ := by
    intro hpi
    exact (Set.disjoint_left.mp (octagonBasePingPongSet_pairwise_disjoint hij)) hpi hp
  have himgne :
      (octagonBaseToPGL23.comp (octagonBaseFactorInclusion i)) h ≠ 1 := by
    intro him
    apply hh
    apply octagonBaseFactorToPGL23_injective i
    simpa using him
  cases i with
  | handle =>
      rcases h.property with ⟨n, hn⟩
      have hn0 : n ≠ 0 := by
        intro hnzero
        apply hh
        apply Subtype.ext
        change (h : OctagonBaseGroup) = 1
        rw [← hn, hnzero]
        simp
      have hmap :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .handle)) h =
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.A true))) ^ n := by
        change octagonBaseToPGL23 (h : OctagonBaseGroup) = _
        rw [← hn, map_zpow, octagonBaseToPGL23_factorElement]
      rw [hmap]
      exact octagonA_zpow_maps_compl_handleSet n hn0 hpcompl
  | cone1 =>
      rcases h.property with ⟨n, hn⟩
      have hmap :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone1)) h =
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B true false))) ^ n := by
        change octagonBaseToPGL23 (h : OctagonBaseGroup) = _
        rw [← hn, map_zpow, octagonBaseToPGL23_factorElement]
      have himage :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone1)) h =
          BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B true false)) := by
        rw [hmap]
        exact zpow_eq_self_of_orderOf_eq_two
          (orderOf_toPGL23_octagon_B true false) n (hmap ▸ himgne)
      rw [himage]
      exact octagonB_maps_compl_basePingPongSet true false hpcompl
  | cone2 =>
      rcases h.property with ⟨n, hn⟩
      have hmap :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone2)) h =
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B false false))) ^ n := by
        change octagonBaseToPGL23 (h : OctagonBaseGroup) = _
        rw [← hn, map_zpow, octagonBaseToPGL23_factorElement]
      have himage :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone2)) h =
          BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B false false)) := by
        rw [hmap]
        exact zpow_eq_self_of_orderOf_eq_two
          (orderOf_toPGL23_octagon_B false false) n (hmap ▸ himgne)
      rw [himage]
      exact octagonB_maps_compl_basePingPongSet false false hpcompl
  | cone3 =>
      rcases h.property with ⟨n, hn⟩
      have hmap :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone3)) h =
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B false true))) ^ n := by
        change octagonBaseToPGL23 (h : OctagonBaseGroup) = _
        rw [← hn, map_zpow, octagonBaseToPGL23_factorElement]
      have himage :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone3)) h =
          BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B false true)) := by
        rw [hmap]
        exact zpow_eq_self_of_orderOf_eq_two
          (orderOf_toPGL23_octagon_B false true) n (hmap ▸ himgne)
      rw [himage]
      exact octagonB_maps_compl_basePingPongSet false true hpcompl
  | cone4 =>
      rcases h.property with ⟨n, hn⟩
      have hmap :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone4)) h =
          (BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B true true))) ^ n := by
        change octagonBaseToPGL23 (h : OctagonBaseGroup) = _
        rw [← hn, map_zpow, octagonBaseToPGL23_factorElement]
      have himage :
          (octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion .cone4)) h =
          BuserSarnakQuaternionUnit.toPGL23
            (octagonUnit (.B true true)) := by
        rw [hmap]
        exact zpow_eq_self_of_orderOf_eq_two
          (orderOf_toPGL23_octagon_B true true) n (hmap ▸ himgne)
      rw [himage]
      exact octagonB_maps_compl_basePingPongSet true true hpcompl

/-- The coproduct lift of the five cyclic factor representations is faithful. -/
theorem octagonBaseFreeProductToPGL23_injective :
    Function.Injective
      (Monoid.CoprodI.lift
        (fun i => octagonBaseToPGL23.comp
          (octagonBaseFactorInclusion i))) := by
  letI : Nontrivial OctagonBaseFactor :=
    ⟨⟨OctagonBaseFactor.handle, .cone1, by decide⟩⟩
  apply Monoid.CoprodI.lift_injective_of_ping_pong
    (fun i => octagonBaseToPGL23.comp (octagonBaseFactorInclusion i))
    (Or.inl three_le_card_octagonBaseFactor) octagonBasePingPongSet
  · exact octagonBasePingPongSet_nonempty
  · exact octagonBasePingPongSet_pairwise_disjoint
  · intro i j hij h hh q hq
    have hpre :
        ((octagonBaseToPGL23.comp (octagonBaseFactorInclusion i)) h)⁻¹ • q ∈
          octagonBasePingPongSet j := Set.mem_smul_set_iff_inv_smul_mem.mp hq
    have hm := octagonBaseFactor_pingPong hij h hh hpre
    simpa using hm

/-- The explicit PGL representation is faithful on the entire octagon HNN
base group. -/
theorem octagonBaseToPGL23_injective :
    Function.Injective octagonBaseToPGL23 :=
  octagonBaseToPGL23_injective_iff_freeProductLift.mpr
    octagonBaseFreeProductToPGL23_injective

end

end SystolicGrowth
