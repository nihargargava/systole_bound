module

public import Mathlib
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Core.SystolicCore

@[expose] public section

open scoped MatrixGroups Pointwise
open Matrix.SpecialLinearGroup UpperHalfPlane

namespace SystolicGrowth

/-! ## The integral congruence calculation in Buser--Sarnak

The arithmetic surface construction starts with norm-one elements in an
indefinite quaternion algebra. This file proves their congruence trace bound,
discreteness, freeness and cocompactness. Later modules supply the genus
calculation and surface-group marking.
-/

/-- Integral coordinates of a norm-one element in the quaternion algebra with
`i^2 = a`, `j^2 = b`, and `ij = -ji`. -/
structure BuserSarnakQuaternionUnit (a b : ℤ) where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  norm_one : x0 ^ 2 - a * x1 ^ 2 - b * x2 ^ 2 + (a * b) * x3 ^ 2 = 1

/-- The real matrix realization of the quaternion algebra used in
Buser--Sarnak equation (4.2). -/
noncomputable def buserSarnakMatrix
    (a b x0 x1 x2 x3 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x0 + x1 * Real.sqrt a, Real.sqrt b * (x2 + x3 * Real.sqrt a);
    Real.sqrt b * (x2 - x3 * Real.sqrt a), x0 - x1 * Real.sqrt a]

/-- The determinant of the matrix realization is the quaternion norm. -/
theorem det_buserSarnakMatrix
    (a b x0 x1 x2 x3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (buserSarnakMatrix a b x0 x1 x2 x3).det =
      x0 ^ 2 - a * x1 ^ 2 - b * x2 ^ 2 + (a * b) * x3 ^ 2 := by
  rw [Matrix.det_fin_two]
  change
    (x0 + x1 * Real.sqrt a) * (x0 - x1 * Real.sqrt a) -
        (Real.sqrt b * (x2 + x3 * Real.sqrt a)) *
          (Real.sqrt b * (x2 - x3 * Real.sqrt a)) =
      x0 ^ 2 - a * x1 ^ 2 - b * x2 ^ 2 + (a * b) * x3 ^ 2
  calc
    _ = x0 ^ 2 - (Real.sqrt a) ^ 2 * x1 ^ 2 - (Real.sqrt b) ^ 2 * x2 ^ 2 +
          ((Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2) * x3 ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The matrix attached to an integral norm-one quaternion. -/
noncomputable def BuserSarnakQuaternionUnit.matrix
    {a b : ℤ} (x : BuserSarnakQuaternionUnit a b) : Matrix (Fin 2) (Fin 2) ℝ :=
  buserSarnakMatrix (a : ℝ) (b : ℝ) x.x0 x.x1 x.x2 x.x3

/-- Integral norm-one quaternions map to determinant-one matrices. -/
theorem BuserSarnakQuaternionUnit.matrix_det
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : BuserSarnakQuaternionUnit a b) :
    x.matrix.det = 1 := by
  rw [BuserSarnakQuaternionUnit.matrix, det_buserSarnakMatrix]
  · exact_mod_cast x.norm_one
  · exact_mod_cast ha
  · exact_mod_cast hb

/-- The resulting element of `SL(2, ℝ)`. -/
noncomputable def BuserSarnakQuaternionUnit.toSL
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : BuserSarnakQuaternionUnit a b) :
    SL(2, ℝ) :=
  ⟨x.matrix, x.matrix_det ha hb⟩

/-- The trace in the matrix realization is twice the scalar quaternion
coefficient. -/
theorem trace_buserSarnakMatrix (a b x0 x1 x2 x3 : ℝ) :
    Matrix.trace (buserSarnakMatrix a b x0 x1 x2 x3) = 2 * x0 := by
  rw [Matrix.trace, Fin.sum_univ_two]
  change (x0 + x1 * Real.sqrt a) + (x0 - x1 * Real.sqrt a) = 2 * x0
  ring

/-- Trace formula for an integral norm-one quaternion. -/
theorem BuserSarnakQuaternionUnit.trace_matrix
    {a b : ℤ} (x : BuserSarnakQuaternionUnit a b) :
    Matrix.trace x.matrix = 2 * (x.x0 : ℝ) := by
  simpa [BuserSarnakQuaternionUnit.matrix] using
    trace_buserSarnakMatrix (a : ℝ) (b : ℝ) x.x0 x.x1 x.x2 x.x3

namespace BuserSarnakQuaternionUnit

/-- Equality of integral quaternion units is determined by their four
coordinates. -/
@[ext] theorem ext {a b : ℤ} {x y : BuserSarnakQuaternionUnit a b}
    (h0 : x.x0 = y.x0) (h1 : x.x1 = y.x1) (h2 : x.x2 = y.x2)
    (h3 : x.x3 = y.x3) : x = y := by
  cases x
  cases y
  simp_all

/-- Quaternion multiplication in coordinates for `i^2 = a`, `j^2 = b`, and
`ij = -ji`. -/
def mul {a b : ℤ} (x y : BuserSarnakQuaternionUnit a b) :
    BuserSarnakQuaternionUnit a b where
  x0 := x.x0 * y.x0 + a * x.x1 * y.x1 + b * x.x2 * y.x2 - (a * b) * x.x3 * y.x3
  x1 := x.x0 * y.x1 + x.x1 * y.x0 - b * x.x2 * y.x3 + b * x.x3 * y.x2
  x2 := x.x0 * y.x2 + x.x2 * y.x0 + a * x.x1 * y.x3 - a * x.x3 * y.x1
  x3 := x.x0 * y.x3 + x.x3 * y.x0 + x.x1 * y.x2 - x.x2 * y.x1
  norm_one := by
    calc
      _ = (x.x0 ^ 2 - a * x.x1 ^ 2 - b * x.x2 ^ 2 + (a * b) * x.x3 ^ 2) *
          (y.x0 ^ 2 - a * y.x1 ^ 2 - b * y.x2 ^ 2 + (a * b) * y.x3 ^ 2) := by ring
      _ = 1 := by rw [x.norm_one, y.norm_one]; norm_num

/-- The identity quaternion. -/
def one (a b : ℤ) : BuserSarnakQuaternionUnit a b :=
  ⟨1, 0, 0, 0, by norm_num⟩

/-- Conjugation is inversion on the norm-one locus. -/
def inv {a b : ℤ} (x : BuserSarnakQuaternionUnit a b) :
    BuserSarnakQuaternionUnit a b :=
  ⟨x.x0, -x.x1, -x.x2, -x.x3, by simpa using x.norm_one⟩

instance instMul (a b : ℤ) : Mul (BuserSarnakQuaternionUnit a b) := ⟨mul⟩
instance instOne (a b : ℤ) : One (BuserSarnakQuaternionUnit a b) := ⟨one a b⟩
instance instInv (a b : ℤ) : Inv (BuserSarnakQuaternionUnit a b) := ⟨inv⟩

/-- The integral norm-one quaternions form a group. -/
instance instGroup (a b : ℤ) : Group (BuserSarnakQuaternionUnit a b) where
  mul_assoc x y z := by
    change mul (mul x y) z = mul x (mul y z)
    ext <;> simp [mul] <;> ring
  one_mul x := by
    change mul (one a b) x = x
    ext <;> simp [mul, one] <;> ring
  mul_one x := by
    change mul x (one a b) = x
    ext <;> simp [mul, one] <;> ring
  inv_mul_cancel x := by
    change mul (inv x) x = one a b
    ext <;> simp [mul, inv, one]
    · simpa [pow_two, sub_eq_add_neg, mul_assoc] using x.norm_one
    · ring
    · ring
    · ring

end BuserSarnakQuaternionUnit

/-- The matrix realization respects quaternion multiplication. -/
theorem BuserSarnakQuaternionUnit.matrix_mul
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x y : BuserSarnakQuaternionUnit a b) :
    (x * y).matrix = x.matrix * y.matrix := by
  change (BuserSarnakQuaternionUnit.mul x y).matrix = x.matrix * y.matrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
      BuserSarnakQuaternionUnit.mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    have ha' : (Real.sqrt (a : ℝ)) ^ 2 = (a : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast ha)
    have hb' : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hb)
    ring_nf
    simp only [ha', hb']
    ring

/-- The norm-one integral quaternion group maps to `SL(2, ℝ)` by the
Buser--Sarnak matrix realization. -/
noncomputable def BuserSarnakQuaternionUnit.toSLHom
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BuserSarnakQuaternionUnit a b →* SL(2, ℝ) where
  toFun := BuserSarnakQuaternionUnit.toSL ha hb
  map_one' := by
    change BuserSarnakQuaternionUnit.toSL ha hb (BuserSarnakQuaternionUnit.one a b) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [BuserSarnakQuaternionUnit.toSL, BuserSarnakQuaternionUnit.matrix,
        buserSarnakMatrix, BuserSarnakQuaternionUnit.one]
  map_mul' x y := by
    ext i j
    exact congr_fun (congr_fun (BuserSarnakQuaternionUnit.matrix_mul ha hb x y) i) j

/-- The coordinate form of membership in the principal level-`p` subgroup.
The scalar coordinate is congruent to `1`, while the other coordinates vanish
modulo `p`. -/
@[ext]
structure BuserSarnakQuaternionMod (p : ℕ) [NeZero p] where
  x0 : ZMod p
  x1 : ZMod p
  x2 : ZMod p
  x3 : ZMod p
deriving DecidableEq, Fintype

namespace BuserSarnakQuaternionMod

def one (p : ℕ) [NeZero p] : BuserSarnakQuaternionMod p :=
  ⟨1, 0, 0, 0⟩

def mul {p : ℕ} [NeZero p] (x y : BuserSarnakQuaternionMod p) :
    BuserSarnakQuaternionMod p :=
  ⟨x.x0 * y.x0 + 2 * x.x1 * y.x1 + 3 * x.x2 * y.x2 - 6 * x.x3 * y.x3,
    x.x0 * y.x1 + x.x1 * y.x0 - 3 * x.x2 * y.x3 + 3 * x.x3 * y.x2,
    x.x0 * y.x2 + x.x2 * y.x0 + 2 * x.x1 * y.x3 - 2 * x.x3 * y.x1,
    x.x0 * y.x3 + x.x3 * y.x0 + x.x1 * y.x2 - x.x2 * y.x1⟩

instance instMonoid (p : ℕ) [NeZero p] : Monoid (BuserSarnakQuaternionMod p) where
  one := one p
  mul := mul
  one_mul x := by
    change mul (one p) x = x
    ext <;> simp [one, mul]
  mul_one x := by
    change mul x (one p) = x
    ext <;> simp [one, mul]
  mul_assoc x y z := by
    change mul (mul x y) z = mul x (mul y z)
    ext <;> simp [mul] <;> ring

@[simp] theorem one_x0 (p : ℕ) [NeZero p] :
    (1 : BuserSarnakQuaternionMod p).x0 = 1 := rfl

@[simp] theorem one_x1 (p : ℕ) [NeZero p] :
    (1 : BuserSarnakQuaternionMod p).x1 = 0 := rfl

@[simp] theorem one_x2 (p : ℕ) [NeZero p] :
    (1 : BuserSarnakQuaternionMod p).x2 = 0 := rfl

@[simp] theorem one_x3 (p : ℕ) [NeZero p] :
    (1 : BuserSarnakQuaternionMod p).x3 = 0 := rfl

@[simp] theorem mul_x0 {p : ℕ} [NeZero p]
    (x y : BuserSarnakQuaternionMod p) :
    (x * y).x0 = x.x0 * y.x0 + 2 * x.x1 * y.x1 + 3 * x.x2 * y.x2 - 6 * x.x3 * y.x3 := rfl

@[simp] theorem mul_x1 {p : ℕ} [NeZero p]
    (x y : BuserSarnakQuaternionMod p) :
    (x * y).x1 = x.x0 * y.x1 + x.x1 * y.x0 - 3 * x.x2 * y.x3 + 3 * x.x3 * y.x2 := rfl

@[simp] theorem mul_x2 {p : ℕ} [NeZero p]
    (x y : BuserSarnakQuaternionMod p) :
    (x * y).x2 = x.x0 * y.x2 + x.x2 * y.x0 + 2 * x.x1 * y.x3 - 2 * x.x3 * y.x1 := rfl

@[simp] theorem mul_x3 {p : ℕ} [NeZero p]
    (x y : BuserSarnakQuaternionMod p) :
    (x * y).x3 = x.x0 * y.x3 + x.x3 * y.x0 + x.x1 * y.x2 - x.x2 * y.x1 := rfl

end BuserSarnakQuaternionMod

namespace BuserSarnakQuaternionUnit

/-- Coordinatewise reduction of the integral `(2,3)` quaternion order modulo `p`. -/
def reductionMod (p : ℕ) [NeZero p] :
    BuserSarnakQuaternionUnit 2 3 →* BuserSarnakQuaternionMod p where
  toFun x := ⟨x.x0, x.x1, x.x2, x.x3⟩
  map_one' := by
    have hone : BuserSarnakQuaternionUnit.one 2 3 =
        (1 : BuserSarnakQuaternionUnit 2 3) := by
      apply mul_left_cancel (a := BuserSarnakQuaternionUnit.one 2 3)
      rw [mul_one]
      change BuserSarnakQuaternionUnit.mul
        (BuserSarnakQuaternionUnit.one 2 3) (BuserSarnakQuaternionUnit.one 2 3) =
          BuserSarnakQuaternionUnit.one 2 3
      ext <;> norm_num [BuserSarnakQuaternionUnit.mul, BuserSarnakQuaternionUnit.one]
    rw [← hone]
    ext <;> norm_num [BuserSarnakQuaternionUnit.one]
  map_mul' x y := by
    change
      (⟨(x.x0 * y.x0 + 2 * x.x1 * y.x1 + 3 * x.x2 * y.x2 - 6 * x.x3 * y.x3 : ℤ),
          (x.x0 * y.x1 + x.x1 * y.x0 - 3 * x.x2 * y.x3 + 3 * x.x3 * y.x2 : ℤ),
          (x.x0 * y.x2 + x.x2 * y.x0 + 2 * x.x1 * y.x3 - 2 * x.x3 * y.x1 : ℤ),
          (x.x0 * y.x3 + x.x3 * y.x0 + x.x1 * y.x2 - x.x2 * y.x1 : ℤ)⟩ :
        BuserSarnakQuaternionMod p) =
        (⟨x.x0, x.x1, x.x2, x.x3⟩ : BuserSarnakQuaternionMod p) *
          ⟨y.x0, y.x1, y.x2, y.x3⟩
    ext <;>
      simp only [BuserSarnakQuaternionMod.mul_x0, BuserSarnakQuaternionMod.mul_x1,
        BuserSarnakQuaternionMod.mul_x2, BuserSarnakQuaternionMod.mul_x3] <;>
      push_cast <;> ring

theorem reductionMod_eq_one_iff (p : ℕ) [NeZero p]
    (x : BuserSarnakQuaternionUnit 2 3) :
    reductionMod p x = 1 ↔
      (p : ℤ) ∣ x.x0 - 1 ∧ (p : ℤ) ∣ x.x1 ∧
        (p : ℤ) ∣ x.x2 ∧ (p : ℤ) ∣ x.x3 := by
  constructor
  · intro hx
    have h0 : (x.x0 : ZMod p) = 1 :=
      congrArg BuserSarnakQuaternionMod.x0 hx
    have h1 : (x.x1 : ZMod p) = 0 :=
      congrArg BuserSarnakQuaternionMod.x1 hx
    have h2 : (x.x2 : ZMod p) = 0 :=
      congrArg BuserSarnakQuaternionMod.x2 hx
    have h3 : (x.x3 : ZMod p) = 0 :=
      congrArg BuserSarnakQuaternionMod.x3 hx
    have h0' : ((x.x0 - 1 : ℤ) : ZMod p) = 0 := by
      simpa using sub_eq_zero.mpr h0
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0',
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have h0' : ((x.x0 - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h0
    have h1' : (x.x1 : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
    have h2' : (x.x2 : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
    have h3' : (x.x3 : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3
    have h0'' : (x.x0 : ZMod p) = 1 := sub_eq_zero.mp (by simpa using h0')
    ext <;> simp [reductionMod, h0'', h1', h2', h3']

end BuserSarnakQuaternionUnit

def BuserSarnakQuaternionUnit.InPrincipalCongruence
    {a b : ℤ} (p : ℤ) (x : BuserSarnakQuaternionUnit a b) : Prop :=
  p ∣ x.x0 - 1 ∧ p ∣ x.x1 ∧ p ∣ x.x2 ∧ p ∣ x.x3

/-- A principal-congruence quaternion unit has scalar coefficient whose square
is `1` modulo `p^2`.  This is the congruence calculation behind equation (4.4)
of Buser--Sarnak. -/
theorem BuserSarnakQuaternionUnit.square_dvd_x0_sq_sub_one
    {a b p : ℤ} (x : BuserSarnakQuaternionUnit a b)
    (hx : x.InPrincipalCongruence p) :
    p ^ 2 ∣ x.x0 ^ 2 - 1 := by
  rcases hx with ⟨-, hx1, hx2, hx3⟩
  rcases hx1 with ⟨y1, hy1⟩
  rcases hx2 with ⟨y2, hy2⟩
  rcases hx3 with ⟨y3, hy3⟩
  refine ⟨a * y1 ^ 2 + b * y2 ^ 2 - (a * b) * y3 ^ 2, ?_⟩
  have hnorm := x.norm_one
  rw [hy1, hy2, hy3] at hnorm
  calc
    x.x0 ^ 2 - 1 =
        a * (p * y1) ^ 2 + b * (p * y2) ^ 2 - (a * b) * (p * y3) ^ 2 := by
          linarith
    _ = p ^ 2 * (a * y1 ^ 2 + b * y2 ^ 2 - (a * b) * y3 ^ 2) := by ring

/-- For an odd prime, the only square roots of `1` modulo `p^2` are `1` and
`-1`.  Applied to the preceding theorem, this is the missing divisibility
step in Buser--Sarnak's equation (4.4). -/
theorem square_dvd_sub_one_or_add_one_of_prime
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) {x : ℤ}
    (hx : (p : ℤ) ^ 2 ∣ x ^ 2 - 1) :
    (p : ℤ) ^ 2 ∣ x - 1 ∨ (p : ℤ) ^ 2 ∣ x + 1 := by
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hproduct : (p : ℤ) ^ 2 ∣ (x - 1) * (x + 1) := by
    convert hx using 1 <;> ring
  have hp_product : (p : ℤ) ∣ (x - 1) * (x + 1) :=
    (dvd_pow_self (p : ℤ) (by norm_num : 2 ≠ 0)).trans hproduct
  have hnotboth : ¬ ((p : ℤ) ∣ x - 1 ∧ (p : ℤ) ∣ x + 1) := by
    rintro ⟨hminus, hplus⟩
    have hp_dvd_two_int : (p : ℤ) ∣ 2 := by
      rw [show (2 : ℤ) = (x + 1) - (x - 1) by ring]
      exact dvd_sub hplus hminus
    have hp_dvd_two : p ∣ 2 := Int.natCast_dvd_natCast.mp hp_dvd_two_int
    apply hp_two
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) hp_dvd_two) hp.two_le
  rcases hp_int.dvd_or_dvd hp_product with hminus | hplus
  · left
    exact hp_int.pow_dvd_of_dvd_mul_right 2
      (fun h => hnotboth ⟨hminus, h⟩) hproduct
  · right
    exact hp_int.pow_dvd_of_dvd_mul_left 2
      (fun h => hnotboth ⟨h, hplus⟩) hproduct

namespace BuserSarnakQuaternionUnit

/-- The principal level-`p` subgroup of the integral norm-one quaternion
group. -/
def principalCongruenceSubgroup {a b : ℤ} (p : ℤ) :
    Subgroup (BuserSarnakQuaternionUnit a b) where
  carrier := {x | x.InPrincipalCongruence p}
  one_mem' := by
    change (one a b).InPrincipalCongruence p
    simp [BuserSarnakQuaternionUnit.InPrincipalCongruence, one]
  mul_mem' {x y} hx hy := by
    change (mul x y).InPrincipalCongruence p
    rcases hx with ⟨hx0, hx1, hx2, hx3⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3⟩
    have h00 : p ∣ x.x0 * y.x0 - 1 := by
      rw [show x.x0 * y.x0 - 1 = (x.x0 - 1) * y.x0 + (y.x0 - 1) by ring]
      exact dvd_add (dvd_mul_of_dvd_left hx0 _) hy0
    have h11 : p ∣ a * x.x1 * y.x1 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx1 a) y.x1
    have h22 : p ∣ b * x.x2 * y.x2 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx2 b) y.x2
    have h33 : p ∣ (a * b) * x.x3 * y.x3 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx3 (a * b)) y.x3
    have h1a : p ∣ x.x0 * y.x1 := dvd_mul_of_dvd_right hy1 x.x0
    have h1b : p ∣ x.x1 * y.x0 := dvd_mul_of_dvd_left hx1 y.x0
    have h1c : p ∣ b * x.x2 * y.x3 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx2 b) y.x3
    have h1d : p ∣ b * x.x3 * y.x2 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx3 b) y.x2
    have h2a : p ∣ x.x0 * y.x2 := dvd_mul_of_dvd_right hy2 x.x0
    have h2b : p ∣ x.x2 * y.x0 := dvd_mul_of_dvd_left hx2 y.x0
    have h2c : p ∣ a * x.x1 * y.x3 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx1 a) y.x3
    have h2d : p ∣ a * x.x3 * y.x1 := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx3 a) y.x1
    have h3a : p ∣ x.x0 * y.x3 := dvd_mul_of_dvd_right hy3 x.x0
    have h3b : p ∣ x.x3 * y.x0 := dvd_mul_of_dvd_left hx3 y.x0
    have h3c : p ∣ x.x1 * y.x2 := dvd_mul_of_dvd_left hx1 y.x2
    have h3d : p ∣ x.x2 * y.x1 := dvd_mul_of_dvd_left hx2 y.x1
    refine ⟨?_, ?_, ?_, ?_⟩
    · change p ∣ x.x0 * y.x0 + a * x.x1 * y.x1 + b * x.x2 * y.x2 -
        (a * b) * x.x3 * y.x3 - 1
      rw [show x.x0 * y.x0 + a * x.x1 * y.x1 + b * x.x2 * y.x2 -
          (a * b) * x.x3 * y.x3 - 1 =
          (x.x0 * y.x0 - 1) + a * x.x1 * y.x1 + b * x.x2 * y.x2 -
            (a * b) * x.x3 * y.x3 by ring]
      exact dvd_sub (dvd_add (dvd_add h00 h11) h22) h33
    · simpa [mul, sub_eq_add_neg, add_assoc] using
        dvd_add (dvd_sub (dvd_add h1a h1b) h1c) h1d
    · simpa [mul, sub_eq_add_neg, add_assoc] using
        dvd_sub (dvd_add (dvd_add h2a h2b) h2c) h2d
    · simpa [mul, sub_eq_add_neg, add_assoc] using
        dvd_sub (dvd_add (dvd_add h3a h3b) h3c) h3d
  inv_mem' {x} hx := by
    change (inv x).InPrincipalCongruence p
    rcases hx with ⟨hx0, hx1, hx2, hx3⟩
    exact ⟨by simpa [inv], by simpa [inv] using dvd_neg.mpr hx1,
      by simpa [inv] using dvd_neg.mpr hx2, by simpa [inv] using dvd_neg.mpr hx3⟩

/-- The Buser--Sarnak level group, realized as a concrete subgroup of
`SL(2, ℝ)`.  The remaining work is to prove its geometric quotient properties. -/
theorem principalCongruenceSubgroup23_eq_ker_reductionUnits (p : ℕ) [NeZero p] :
    principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ) =
      (reductionMod p).toHomUnits.ker := by
  rw [MonoidHom.ker_toHomUnits]
  ext x
  change InPrincipalCongruence (p : ℤ) x ↔ reductionMod p x = 1
  exact (reductionMod_eq_one_iff p x).symm

theorem principalCongruenceSubgroup23_finiteIndex (p : ℕ) [NeZero p] :
    (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ)).FiniteIndex := by
  rw [principalCongruenceSubgroup23_eq_ker_reductionUnits]
  exact Subgroup.finiteIndex_ker (reductionMod p).toHomUnits

/-- The full integral `(2,3)` quaternion group in its matrix realization. -/
noncomputable def fullDeckGroup23 : Subgroup SL(2, ℝ) :=
  (toSLHom (a := 2) (b := 3) (by norm_num) (by norm_num)).range

/-- The tautological surjection from integral quaternion units onto their
matrix-image group. -/
noncomputable def toFullDeckGroup23 :
    BuserSarnakQuaternionUnit 2 3 →* fullDeckGroup23 :=
  (toSLHom (a := 2) (b := 3) (by norm_num) (by norm_num)).codRestrict
    fullDeckGroup23 (fun x ↦ ⟨x, rfl⟩)

theorem toFullDeckGroup23_surjective : Function.Surjective toFullDeckGroup23 := by
  rintro ⟨gamma, x, rfl⟩
  exact ⟨x, Subtype.ext rfl⟩

/-- The principal level, regarded as a subgroup of the full arithmetic
matrix-image group. -/
noncomputable def levelSubgroupOfFull23 (p : ℕ) : Subgroup fullDeckGroup23 :=
  (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ)).map toFullDeckGroup23

theorem levelSubgroupOfFull23_finiteIndex (p : ℕ) [NeZero p] :
    (levelSubgroupOfFull23 p).FiniteIndex := by
  letI : (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ)).FiniteIndex :=
    principalCongruenceSubgroup23_finiteIndex p
  exact Subgroup.FiniteIndex.map_of_surjective
    (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ))
    toFullDeckGroup23 toFullDeckGroup23_surjective

noncomputable def levelDeckGroup {a b : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℤ) : Subgroup SL(2, ℝ) :=
  (principalCongruenceSubgroup p).map (toSLHom ha hb)

theorem levelSubgroupOfFull23_eq_subgroupOf (p : ℕ) :
    levelSubgroupOfFull23 p =
      (levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)).subgroupOf
        fullDeckGroup23 := by
  ext gamma
  change gamma ∈
      (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ)).map toFullDeckGroup23 ↔
    (gamma : SL(2, ℝ)) ∈
      (principalCongruenceSubgroup (a := 2) (b := 3) (p : ℤ)).map
        (toSLHom (by norm_num) (by norm_num))
  constructor
  · rintro ⟨x, hx, hxgamma⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg Subtype.val hxgamma
  · rintro ⟨x, hx, hxgamma⟩
    refine ⟨x, hx, ?_⟩
    exact Subtype.ext hxgamma

theorem levelDeckGroup_one_eq_fullDeckGroup23 :
    levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (1 : ℤ) =
      fullDeckGroup23 := by
  ext gamma
  simp [levelDeckGroup, fullDeckGroup23, principalCongruenceSubgroup,
    InPrincipalCongruence]

/-- One compact fundamental set for the full integral arithmetic group gives
compact quotients for all nonzero principal levels. -/
theorem levelDeckGroup23_compactQuotient_of_full_compact_cover
    (K : Set ℍ) (hK : IsCompact K)
    (hcover : ∀ z : ℍ, ∃ gamma : fullDeckGroup23, gamma • z ∈ K)
    (p : ℕ) [NeZero p] :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient
      (levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)) ℍ)) := by
  letI : (levelSubgroupOfFull23 p).FiniteIndex :=
    levelSubgroupOfFull23_finiteIndex p
  obtain ⟨t, -, ht⟩ :=
    Subgroup.exists_leftTransversal_of_FiniteIndex
      (D := levelSubgroupOfFull23 p) (H := ⊤) le_top
  let Kp : Set ℍ :=
    ⋃ r ∈ t, (fun z : ℍ ↦ ((r : fullDeckGroup23)⁻¹ • z)) '' K
  have hKp : IsCompact Kp := by
    exact t.isCompact_biUnion fun r _ ↦
      hK.image (continuous_const_smul (r : fullDeckGroup23)⁻¹)
  have hlevelCover : ∀ z : ℍ, ∃ gamma :
      levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ),
      gamma • z ∈ Kp := by
    intro z
    obtain ⟨g, hgK⟩ := hcover z
    have hgUnion : g ∈
        ⋃ r ∈ t, (r : fullDeckGroup23) •
          (levelSubgroupOfFull23 p : Set fullDeckGroup23) := by
      rw [ht]
      exact Subgroup.mem_top g
    obtain ⟨r, hgUnion⟩ := Set.mem_iUnion.mp hgUnion
    obtain ⟨hr, hgCoset⟩ := Set.mem_iUnion.mp hgUnion
    let h : fullDeckGroup23 := (r : fullDeckGroup23)⁻¹ * g
    have hh : h ∈ levelSubgroupOfFull23 p :=
      (mem_leftCoset_iff (s := (levelSubgroupOfFull23 p : Set fullDeckGroup23))
        (r : fullDeckGroup23)).mp hgCoset
    have hmul : (r : fullDeckGroup23) * h = g := by
      simp [h]
    have hh' : (h : SL(2, ℝ)) ∈
        levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ) := by
      have hsub : h ∈
          (levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)).subgroupOf
            fullDeckGroup23 := by
        rw [← levelSubgroupOfFull23_eq_subgroupOf p]
        exact hh
      exact hsub
    refine ⟨⟨h, hh'⟩, ?_⟩
    simp only [Kp, Set.mem_iUnion]
    refine ⟨r, ⟨hr, ?_⟩⟩
    refine ⟨g • z, hgK, ?_⟩
    rw [← hmul]
    change (r : fullDeckGroup23)⁻¹ •
      (((r : fullDeckGroup23) * h) • z) = h • z
    rw [mul_smul, inv_smul_smul]
  exact isCompact_orbitRel_quotient_of_compact_cover Kp hKp hlevelCover

/-- Membership in the concrete level group has a quaternion-coordinate
witness satisfying the principal congruences. -/
theorem exists_unit_of_mem_levelDeckGroup
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℤ) {gamma : SL(2, ℝ)}
    (hgamma : gamma ∈ levelDeckGroup ha hb p) :
    ∃ x : BuserSarnakQuaternionUnit a b,
      x.InPrincipalCongruence p ∧ gamma = x.toSL ha hb := by
  rcases hgamma with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

end BuserSarnakQuaternionUnit

/-- The four real matrix entries of an element of `SL(2, ℝ)`, in row-major
order.  This is an injective continuous coordinate map into a normed vector
space, which lets us prove discreteness using an explicit integer lattice. -/
noncomputable def specialLinearEntries (gamma : SL(2, ℝ)) : Fin 4 → ℝ :=
  ![gamma 0 0, gamma 0 1, gamma 1 0, gamma 1 1]

theorem specialLinearEntries_injective : Function.Injective specialLinearEntries := by
  intro gamma delta h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [specialLinearEntries] using congr_fun h 0
  · simpa [specialLinearEntries] using congr_fun h 1
  · simpa [specialLinearEntries] using congr_fun h 2
  · simpa [specialLinearEntries] using congr_fun h 3

theorem continuous_specialLinearEntries : Continuous specialLinearEntries := by
  change Continuous fun gamma : SL(2, ℝ) ↦
    ![gamma 0 0, gamma 0 1, gamma 1 0, gamma 1 1]
  fun_prop

/-- The Buser--Sarnak coordinate change from quaternion coefficients to matrix
entries. -/
noncomputable def buserSarnakEntryEquiv (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v :=
    ![v 0 + v 1 * Real.sqrt a, Real.sqrt b * (v 2 + v 3 * Real.sqrt a),
      Real.sqrt b * (v 2 - v 3 * Real.sqrt a), v 0 - v 1 * Real.sqrt a]
  invFun v :=
    ![(v 0 + v 3) / 2,
      (v 0 - v 3) / (2 * Real.sqrt a),
      (v 1 + v 2) / (2 * Real.sqrt b),
      (v 1 - v 2) / (2 * Real.sqrt a * Real.sqrt b)]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp <;>
      field_simp [Real.sqrt_ne_zero'.mpr ha, Real.sqrt_ne_zero'.mpr hb] <;> ring
  right_inv v := by
    funext i
    fin_cases i <;> simp <;>
      field_simp [Real.sqrt_ne_zero'.mpr ha, Real.sqrt_ne_zero'.mpr hb] <;> ring

/-- The real basis obtained by applying the Buser--Sarnak coordinate change to
the standard basis of four-tuples. -/
noncomputable def buserSarnakEntryBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  (Pi.basisFun ℝ (Fin 4)).map (buserSarnakEntryEquiv a b ha hb)

/-- The integer lattice of Buser--Sarnak matrix-entry coordinates. -/
noncomputable def buserSarnakEntryLattice (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Submodule ℤ (Fin 4 → ℝ) :=
  Submodule.span ℤ (Set.range (buserSarnakEntryBasis a b ha hb))

theorem BuserSarnakQuaternionUnit.toSL_mem_buserSarnakEntryLattice
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (x : BuserSarnakQuaternionUnit a b) :
    specialLinearEntries (x.toSL (le_of_lt ha) (le_of_lt hb)) ∈
      buserSarnakEntryLattice (a : ℝ) (b : ℝ)
        (by exact_mod_cast ha) (by exact_mod_cast hb) := by
  rw [buserSarnakEntryLattice,
    (buserSarnakEntryBasis _ _ _ _).mem_span_iff_repr_mem ℤ]
  intro i
  have hcoords : specialLinearEntries (x.toSL (le_of_lt ha) (le_of_lt hb)) =
      buserSarnakEntryEquiv (a : ℝ) (b : ℝ)
        (by exact_mod_cast ha) (by exact_mod_cast hb)
        ![(x.x0 : ℝ), (x.x1 : ℝ), (x.x2 : ℝ), (x.x3 : ℝ)] := by
    funext j
    fin_cases j <;>
      simp [specialLinearEntries, buserSarnakEntryEquiv,
        BuserSarnakQuaternionUnit.toSL, BuserSarnakQuaternionUnit.matrix,
        buserSarnakMatrix]
  rw [hcoords]
  fin_cases i
  · exact ⟨x.x0, by simp [buserSarnakEntryBasis, Module.Basis.map, Pi.basisFun_repr]⟩
  · exact ⟨x.x1, by simp [buserSarnakEntryBasis, Module.Basis.map, Pi.basisFun_repr]⟩
  · exact ⟨x.x2, by simp [buserSarnakEntryBasis, Module.Basis.map, Pi.basisFun_repr]⟩
  · exact ⟨x.x3, by simp [buserSarnakEntryBasis, Module.Basis.map, Pi.basisFun_repr]⟩

theorem buserSarnakEntryLattice_isDiscrete (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsDiscrete (buserSarnakEntryLattice a b ha hb : Set (Fin 4 → ℝ)) := by
  change IsDiscrete (Submodule.span ℤ (Set.range (buserSarnakEntryBasis a b ha hb)) :
    Set (Fin 4 → ℝ))
  exact (inferInstance : DiscreteTopology
    (Submodule.span ℤ (Set.range (buserSarnakEntryBasis a b ha hb)))).isDiscrete

/-- The concrete Buser--Sarnak level group is discrete whenever the two
quaternion parameters are positive. -/
theorem BuserSarnakQuaternionUnit.levelDeckGroup_isDiscrete
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (p : ℤ) :
    IsDiscrete (levelDeckGroup (le_of_lt ha) (le_of_lt hb) p : Set SL(2, ℝ)) := by
  let haR : 0 < (a : ℝ) := by exact_mod_cast ha
  let hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hLattice : IsDiscrete (buserSarnakEntryLattice (a : ℝ) (b : ℝ) haR hbR :
      Set (Fin 4 → ℝ)) :=
    buserSarnakEntryLattice_isDiscrete (a : ℝ) (b : ℝ) haR hbR
  have hPreimage : IsDiscrete (specialLinearEntries ⁻¹'
      (buserSarnakEntryLattice (a : ℝ) (b : ℝ) haR hbR : Set (Fin 4 → ℝ))) :=
    hLattice.preimage continuous_specialLinearEntries.continuousOn
      specialLinearEntries_injective
  apply hPreimage.mono
  rintro gamma hgamma
  rcases exists_unit_of_mem_levelDeckGroup (le_of_lt ha) (le_of_lt hb) p hgamma with
    ⟨x, _, rfl⟩
  exact x.toSL_mem_buserSarnakEntryLattice ha hb

theorem BuserSarnakQuaternionUnit.fullDeckGroup23_isDiscrete :
    IsDiscrete (fullDeckGroup23 : Set SL(2, ℝ)) := by
  rw [← levelDeckGroup_one_eq_fullDeckGroup23]
  exact levelDeckGroup_isDiscrete (a := 2) (b := 3) (by norm_num) (by norm_num) 1

/-- The principal congruence calculation forces the Buser--Sarnak trace to
grow quadratically with the level, away from the two central trace values. -/
theorem BuserSarnakQuaternionUnit.principalCongruence_abs_trace_lower_bound
    {a b : ℤ} {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    {x : BuserSarnakQuaternionUnit a b}
    (hx : x.InPrincipalCongruence (p : ℤ))
    (hx_one : x.x0 ≠ 1) (hx_neg_one : x.x0 ≠ -1) :
    2 * (p : ℤ) ^ 2 - 2 ≤ |2 * x.x0| := by
  have hSquare : (p : ℤ) ^ 2 ∣ x.x0 ^ 2 - 1 :=
    x.square_dvd_x0_sq_sub_one hx
  rcases square_dvd_sub_one_or_add_one_of_prime hp hp_two hSquare with hminus | hplus
  · have hdiv : (p : ℤ) ^ 2 ≤ |x.x0 - 1| :=
      Int.le_abs_of_dvd (sub_ne_zero.mpr hx_one) hminus
    have htri : |x.x0 - 1| ≤ |x.x0| + 1 := by
      simpa using (abs_sub_le x.x0 0 1)
    have hx0 : (p : ℤ) ^ 2 - 1 ≤ |x.x0| := by omega
    have hmul : 2 * ((p : ℤ) ^ 2 - 1) ≤ 2 * |x.x0| :=
      mul_le_mul_of_nonneg_left hx0 (by omega)
    calc
      2 * (p : ℤ) ^ 2 - 2 = 2 * ((p : ℤ) ^ 2 - 1) := by ring
      _ ≤ 2 * |x.x0| := hmul
      _ = |2 * x.x0| := by norm_num [abs_mul]
  · have hdiv : (p : ℤ) ^ 2 ≤ |x.x0 + 1| :=
      Int.le_abs_of_dvd (by omega) hplus
    have htri : |x.x0 + 1| ≤ |x.x0| + 1 := by
      simpa using (abs_add_le x.x0 1)
    have hx0 : (p : ℤ) ^ 2 - 1 ≤ |x.x0| := by omega
    have hmul : 2 * ((p : ℤ) ^ 2 - 1) ≤ 2 * |x.x0| :=
      mul_le_mul_of_nonneg_left hx0 (by omega)
    calc
      2 * (p : ℤ) ^ 2 - 2 = 2 * ((p : ℤ) ^ 2 - 1) := by ring
      _ ≤ 2 * |x.x0| := hmul
      _ = |2 * x.x0| := by norm_num [abs_mul]

/-- Real matrix-trace form of the principal congruence lower bound. -/
theorem BuserSarnakQuaternionUnit.principalCongruence_real_abs_trace_lower_bound
    {a b : ℤ} {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    {x : BuserSarnakQuaternionUnit a b}
    (hx : x.InPrincipalCongruence (p : ℤ))
    (hx_one : x.x0 ≠ 1) (hx_neg_one : x.x0 ≠ -1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (p : ℝ) ^ 2 - 2 ≤
      |((x.toSL ha hb : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  have hInt : 2 * (p : ℤ) ^ 2 - 2 ≤ |2 * x.x0| :=
    x.principalCongruence_abs_trace_lower_bound hp hp_two hx hx_one hx_neg_one
  change 2 * (p : ℝ) ^ 2 - 2 ≤ |x.matrix.trace|
  rw [x.trace_matrix]
  exact_mod_cast hInt

/-! ### A concrete anisotropic quaternion algebra -/

/-- The only way two squares can sum to zero modulo three is for both to
vanish.  This finite calculation drives the elementary infinite-descent proof
of anisotropy below. -/
private theorem zmod_three_sq_add_sq_eq_zero : ∀ u v : ZMod 3,
    u ^ 2 + v ^ 2 = 0 → u = 0 ∧ v = 0 := by
  decide

/-- A zero of the norm form of the quaternion algebra `(2, 3)` is divisible
by three in every coordinate. -/
theorem buserSarnakNorm23_dvd_three {x0 x1 x2 x3 : ℤ}
    (h : x0 ^ 2 - 2 * x1 ^ 2 - 3 * x2 ^ 2 + 6 * x3 ^ 2 = 0) :
    (3 : ℤ) ∣ x0 ∧ (3 : ℤ) ∣ x1 ∧ (3 : ℤ) ∣ x2 ∧ (3 : ℤ) ∣ x3 := by
  have hraw := congrArg (Int.castRingHom (ZMod 3)) h
  norm_num at hraw
  have hmod01 : (x0 : ZMod 3) ^ 2 + (x1 : ZMod 3) ^ 2 = 0 := by
    have reduction : ∀ a b c d : ZMod 3,
        a ^ 2 - 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 = 0 →
          a ^ 2 + b ^ 2 = 0 := by decide
    exact reduction _ _ _ _ hraw
  obtain ⟨hz0, hz1⟩ := zmod_three_sq_add_sq_eq_zero _ _ hmod01
  have hd0 : (3 : ℤ) ∣ x0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x0 3).mp hz0
  have hd1 : (3 : ℤ) ∣ x1 := (ZMod.intCast_zmod_eq_zero_iff_dvd x1 3).mp hz1
  rcases hd0 with ⟨y0, rfl⟩
  rcases hd1 with ⟨y1, rfl⟩
  have hfactor : (3 : ℤ) *
      (3 * y0 ^ 2 - 6 * y1 ^ 2 - x2 ^ 2 + 2 * x3 ^ 2) = 0 := by
    calc
      (3 : ℤ) * (3 * y0 ^ 2 - 6 * y1 ^ 2 - x2 ^ 2 + 2 * x3 ^ 2) =
          (3 * y0) ^ 2 - 2 * (3 * y1) ^ 2 - 3 * x2 ^ 2 + 6 * x3 ^ 2 := by ring
      _ = 0 := h
  have hquot : 3 * y0 ^ 2 - 6 * y1 ^ 2 - x2 ^ 2 + 2 * x3 ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (by norm_num)
  have hraw23 := congrArg (Int.castRingHom (ZMod 3)) hquot
  norm_num at hraw23
  have hmod23 : (x2 : ZMod 3) ^ 2 + (x3 : ZMod 3) ^ 2 = 0 := by
    have reduction : ∀ a b c d : ZMod 3,
        3 * a ^ 2 - 6 * b ^ 2 - c ^ 2 + 2 * d ^ 2 = 0 →
          c ^ 2 + d ^ 2 = 0 := by decide
    exact reduction _ _ _ _ hraw23
  obtain ⟨hz2, hz3⟩ := zmod_three_sq_add_sq_eq_zero _ _ hmod23
  exact ⟨⟨y0, rfl⟩, ⟨y1, rfl⟩,
    (ZMod.intCast_zmod_eq_zero_iff_dvd x2 3).mp hz2,
    (ZMod.intCast_zmod_eq_zero_iff_dvd x3 3).mp hz3⟩

/-- The norm form of the quaternion algebra `(2, 3)` is anisotropic over the
integers.  The proof is an explicit infinite descent using
`buserSarnakNorm23_dvd_three`. -/
theorem buserSarnakNorm23_eq_zero {x0 x1 x2 x3 : ℤ}
    (h : x0 ^ 2 - 2 * x1 ^ 2 - 3 * x2 ^ 2 + 6 * x3 ^ 2 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have auxiliary : ∀ m : ℕ, ∀ y0 y1 y2 y3 : ℤ,
      y0.natAbs + y1.natAbs + y2.natAbs + y3.natAbs = m →
      y0 ^ 2 - 2 * y1 ^ 2 - 3 * y2 ^ 2 + 6 * y3 ^ 2 = 0 →
      y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro y0 y1 y2 y3 hmeasure hnorm
      by_cases hm : m = 0
      · have hy0 : y0.natAbs = 0 := by omega
        have hy1 : y1.natAbs = 0 := by omega
        have hy2 : y2.natAbs = 0 := by omega
        have hy3 : y3.natAbs = 0 := by omega
        exact ⟨Int.natAbs_eq_zero.mp hy0, Int.natAbs_eq_zero.mp hy1,
          Int.natAbs_eq_zero.mp hy2, Int.natAbs_eq_zero.mp hy3⟩
      · rcases buserSarnakNorm23_dvd_three hnorm with ⟨hd0, hd1, hd2, hd3⟩
        rcases hd0 with ⟨z0, rfl⟩
        rcases hd1 with ⟨z1, rfl⟩
        rcases hd2 with ⟨z2, rfl⟩
        rcases hd3 with ⟨z3, rfl⟩
        have hfactor : (9 : ℤ) *
            (z0 ^ 2 - 2 * z1 ^ 2 - 3 * z2 ^ 2 + 6 * z3 ^ 2) = 0 := by
          calc
            (9 : ℤ) * (z0 ^ 2 - 2 * z1 ^ 2 - 3 * z2 ^ 2 + 6 * z3 ^ 2) =
                (3 * z0) ^ 2 - 2 * (3 * z1) ^ 2 - 3 * (3 * z2) ^ 2 +
                  6 * (3 * z3) ^ 2 := by ring
            _ = 0 := hnorm
        have hnormz : z0 ^ 2 - 2 * z1 ^ 2 - 3 * z2 ^ 2 + 6 * z3 ^ 2 = 0 :=
          (mul_eq_zero.mp hfactor).resolve_left (by norm_num)
        let mz := z0.natAbs + z1.natAbs + z2.natAbs + z3.natAbs
        have hmeasureFactor : m = 3 * mz := by
          dsimp [mz]
          rw [← hmeasure]
          simp [Int.natAbs_mul]
          omega
        have hmz : mz < m := by omega
        obtain ⟨hz0, hz1, hz2, hz3⟩ := ih mz hmz z0 z1 z2 z3 (by rfl) hnormz
        simp [hz0, hz1, hz2, hz3]
  exact auxiliary (x0.natAbs + x1.natAbs + x2.natAbs + x3.natAbs) x0 x1 x2 x3 rfl h

/-- In the anisotropic `(2, 3)` algebra, a norm-one integral quaternion with
scalar coordinate one is the identity. -/
theorem BuserSarnakQuaternionUnit.eq_one_of_x0_eq_one
    (x : BuserSarnakQuaternionUnit 2 3) (hx0 : x.x0 = 1) : x = 1 := by
  have hzero : (0 : ℤ) ^ 2 - 2 * x.x1 ^ 2 - 3 * x.x2 ^ 2 + 6 * x.x3 ^ 2 = 0 := by
    rw [show (0 : ℤ) ^ 2 - 2 * x.x1 ^ 2 - 3 * x.x2 ^ 2 + 6 * x.x3 ^ 2 =
        (x.x0 ^ 2 - 2 * x.x1 ^ 2 - 3 * x.x2 ^ 2 + 6 * x.x3 ^ 2) - 1 by
      rw [hx0]
      ring]
    linarith [x.norm_one]
  obtain ⟨-, hx1, hx2, hx3⟩ := buserSarnakNorm23_eq_zero hzero
  change x = BuserSarnakQuaternionUnit.one 2 3
  ext <;> simp [BuserSarnakQuaternionUnit.one, hx0, hx1, hx2, hx3]

/-- A nonidentity unit in the `(2, 3)` algebra cannot have scalar coordinate
one. -/
theorem BuserSarnakQuaternionUnit.x0_ne_one_of_ne_one
    (x : BuserSarnakQuaternionUnit 2 3) (hx : x ≠ 1) : x.x0 ≠ 1 := by
  intro hx0
  exact hx (x.eq_one_of_x0_eq_one hx0)

/-- The principal congruence condition excludes the other central scalar
coordinate when the level is an odd prime. -/
theorem BuserSarnakQuaternionUnit.x0_ne_neg_one_of_principalCongruence
    {a b : ℤ} {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    (x : BuserSarnakQuaternionUnit a b)
    (hx : x.InPrincipalCongruence (p : ℤ)) : x.x0 ≠ -1 := by
  intro hx0
  have hp_dvd_two_int : (p : ℤ) ∣ 2 := by
    have hdiv : (p : ℤ) ∣ -2 := by simpa [hx0] using hx.1
    exact dvd_neg.mp hdiv
  have hp_dvd_two : p ∣ 2 := Int.natCast_dvd_natCast.mp hp_dvd_two_int
  apply hp_two
  exact Nat.le_antisymm (Nat.le_of_dvd (by omega) hp_dvd_two) hp.two_le

/-- For the concrete anisotropic algebra `(2, 3)`, every nonidentity element
of an odd-prime principal congruence subgroup satisfies the Buser--Sarnak
matrix-trace lower bound without any auxiliary noncentrality hypothesis. -/
theorem BuserSarnakQuaternionUnit.nontrivial_principalCongruence_real_abs_trace_lower_bound23
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    (x : BuserSarnakQuaternionUnit 2 3)
    (hx : x.InPrincipalCongruence (p : ℤ)) (hx_ne_one : x ≠ 1) :
    2 * (p : ℝ) ^ 2 - 2 ≤
      |((x.toSL (by norm_num) (by norm_num) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  exact x.principalCongruence_real_abs_trace_lower_bound hp hp_two hx
    (x.x0_ne_one_of_ne_one hx_ne_one)
    (x.x0_ne_neg_one_of_principalCongruence hp hp_two hx) (by norm_num) (by norm_num)

/-- The preceding arithmetic trace estimate applies directly to every
nonidentity element of the concrete level subgroup in `SL(2, ℝ)`. -/
theorem BuserSarnakQuaternionUnit.nontrivial_levelDeckGroup_real_abs_trace_lower_bound23
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) {gamma : SL(2, ℝ)}
    (hgamma : gamma ∈ levelDeckGroup (a := 2) (b := 3)
      (by norm_num) (by norm_num) (p : ℤ))
    (hgamma_ne_one : gamma ≠ 1) :
    2 * (p : ℝ) ^ 2 - 2 ≤ |(gamma : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  rcases exists_unit_of_mem_levelDeckGroup (a := 2) (b := 3)
      (by norm_num) (by norm_num) (p : ℤ) hgamma with ⟨x, hx, rfl⟩
  have hx_ne_one : x ≠ 1 := by
    intro hx_one
    apply hgamma_ne_one
    subst x
    change BuserSarnakQuaternionUnit.toSLHom (by norm_num) (by norm_num) 1 = 1
    exact (BuserSarnakQuaternionUnit.toSLHom (by norm_num) (by norm_num)).map_one
  exact x.nontrivial_principalCongruence_real_abs_trace_lower_bound23 hp hp_two hx hx_ne_one

/-- A real special-linear matrix fixing a point of the upper half-plane is
elliptic or central, hence has absolute trace at most two.  This is proved
directly from the fractional-linear action formula. -/
theorem abs_trace_le_two_of_fixed_point (gamma : SL(2, ℝ)) (z : ℍ)
    (hfix : gamma • z = z) : |(gamma : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤ 2 := by
  have hdet := gamma.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdenom : ((gamma 1 0 : ℂ) * (z : ℂ) + gamma 1 1) ≠ 0 := by
    apply UpperHalfPlane.linear_ne_zero z
    intro hrow
    have hc : gamma 1 0 = 0 := by simpa using congr_fun hrow 0
    have hd : gamma 1 1 = 0 := by simpa using congr_fun hrow 1
    rw [hc, hd] at hdet
    norm_num at hdet
  have hfixed_complex := congrArg (fun w : ℍ ↦ (w : ℂ)) hfix
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hfixed_complex
  have heq : (gamma 0 0 : ℂ) * z + gamma 0 1 =
      z * ((gamma 1 0 : ℂ) * z + gamma 1 1) :=
    (div_eq_iff hdenom).mp hfixed_complex
  have him := congrArg Complex.im heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
  have himfactor : (z : ℂ).im *
      (gamma 0 0 - gamma 1 1 - 2 * gamma 1 0 * (z : ℂ).re) = 0 := by
    linear_combination him
  have hdiff : gamma 0 0 - gamma 1 1 - 2 * gamma 1 0 * (z : ℂ).re = 0 :=
    (mul_eq_zero.mp himfactor).resolve_left z.im_ne_zero
  have hb : gamma 0 1 + gamma 1 0 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) = 0 := by
    linear_combination hre - (z : ℂ).re * hdiff
  have hidentity : (gamma 0 0 + gamma 1 1) ^ 2 +
      4 * (gamma 1 0 * (z : ℂ).im) ^ 2 = 4 := by
    linear_combination
      (gamma 0 0 - gamma 1 1 + 2 * gamma 1 0 * (z : ℂ).re) * hdiff +
        4 * hdet + 4 * gamma 1 0 * hb
  have hsq : (gamma 0 0 + gamma 1 1) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    nlinarith [hidentity, sq_nonneg (2 * gamma 1 0 * (z : ℂ).im)]
  have habs : |gamma 0 0 + gamma 1 1| ≤ |(2 : ℝ)| := (sq_le_sq).mp hsq
  simpa [Matrix.trace, Fin.sum_univ_two] using habs

/-- For every odd prime level, the concrete `(2, 3)` Buser--Sarnak subgroup
acts freely on the upper half-plane. -/
private theorem buserSarnak_re_smul_I (gamma : SL(2, ℝ)) :
    (gamma • (I : ℍ)).re =
      (gamma 0 0 * gamma 1 0 + gamma 0 1 * gamma 1 1) /
        (gamma 1 0 ^ 2 + gamma 1 1 ^ 2) := by
  have hco := UpperHalfPlane.coe_specialLinearGroup_apply gamma (I : ℍ)
  have hre := congrArg Complex.re hco
  change ((↑(gamma • (I : ℍ)) : ℂ).re) = _
  rw [hre]
  norm_num [Complex.div_re, Complex.normSq]
  ring

private theorem buserSarnak_im_smul_I (gamma : SL(2, ℝ)) :
    (gamma • (I : ℍ)).im = 1 / (gamma 1 0 ^ 2 + gamma 1 1 ^ 2) := by
  have hdet := gamma.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hco := UpperHalfPlane.coe_specialLinearGroup_apply gamma (I : ℍ)
  have him := congrArg Complex.im hco
  change ((↑(gamma • (I : ℍ)) : ℂ).im) = _
  rw [him]
  norm_num [Complex.div_im, Complex.normSq]
  have hdet' : gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1 = 1 := by
    convert hdet using 1 <;> ring
  calc
    gamma 0 0 * gamma 1 1 /
        (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0) -
      gamma 0 1 * gamma 1 0 /
        (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0) =
      (gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1) /
        (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0) := by ring
    _ = 1 / (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0) :=
      congrArg (fun t : ℝ ↦
        t / (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0)) hdet'
    _ = (gamma 1 1 * gamma 1 1 + gamma 1 0 * gamma 1 0)⁻¹ := by simp
    _ = _ := by congr 1 <;> ring

private theorem buserSarnak_cosh_smul_I (gamma : SL(2, ℝ)) :
    Real.cosh (dist (I : ℍ) (gamma • I)) =
      (gamma 0 0 ^ 2 + gamma 0 1 ^ 2 + gamma 1 0 ^ 2 + gamma 1 1 ^ 2) / 2 := by
  have hdet := gamma.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdet' : gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1 = 1 := by
    convert hdet using 1 <;> ring
  have hD : gamma 1 0 ^ 2 + gamma 1 1 ^ 2 ≠ 0 := by
    intro hzero
    have hc : gamma 1 0 = 0 := by nlinarith [sq_nonneg (gamma 1 1)]
    have hd : gamma 1 1 = 0 := by nlinarith [sq_nonneg (gamma 1 0)]
    rw [hc, hd] at hdet'
    norm_num at hdet'
  rw [UpperHalfPlane.cosh_dist', buserSarnak_re_smul_I, buserSarnak_im_smul_I]
  norm_num [UpperHalfPlane.coe_I]
  field_simp [hD]
  linear_combination -(gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1 + 1) * hdet'

noncomputable def Internal.BuserSarnakHelpers.hyperboloid0 (z : ℍ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)

noncomputable def Internal.BuserSarnakHelpers.hyperboloid1 (z : ℍ) : ℝ := z.re / z.im

noncomputable def Internal.BuserSarnakHelpers.hyperboloid2 (z : ℍ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im)

private theorem hyperboloid0_eq_cosh_dist_I (z : ℍ) :
    Internal.BuserSarnakHelpers.hyperboloid0 z = Real.cosh (dist (I : ℍ) z) := by
  rw [UpperHalfPlane.cosh_dist']
  norm_num [Internal.BuserSarnakHelpers.hyperboloid0, UpperHalfPlane.coe_I]
  ring

private theorem hyperboloid0_sq_sub_sq_sub_sq (z : ℍ) :
    Internal.BuserSarnakHelpers.hyperboloid0 z ^ 2 - Internal.BuserSarnakHelpers.hyperboloid1 z ^ 2 - Internal.BuserSarnakHelpers.hyperboloid2 z ^ 2 = 1 := by
  have hy : z.im ≠ 0 := z.im_ne_zero
  unfold Internal.BuserSarnakHelpers.hyperboloid0 Internal.BuserSarnakHelpers.hyperboloid1 Internal.BuserSarnakHelpers.hyperboloid2
  field_simp [hy]
  ring

private theorem hyperboloid0_pos (z : ℍ) : 0 < Internal.BuserSarnakHelpers.hyperboloid0 z := by
  rw [hyperboloid0_eq_cosh_dist_I]
  exact lt_of_lt_of_le (by norm_num) (Real.one_le_cosh _)

noncomputable def Internal.BuserSarnakHelpers.matrixHyperboloid0 (gamma : SL(2, ℝ)) : ℝ :=
  (gamma 0 0 ^ 2 + gamma 0 1 ^ 2 + gamma 1 0 ^ 2 + gamma 1 1 ^ 2) / 2

noncomputable def Internal.BuserSarnakHelpers.matrixHyperboloid1 (gamma : SL(2, ℝ)) : ℝ :=
  gamma 0 0 * gamma 1 0 + gamma 0 1 * gamma 1 1

noncomputable def Internal.BuserSarnakHelpers.matrixHyperboloid2 (gamma : SL(2, ℝ)) : ℝ :=
  (gamma 0 0 ^ 2 + gamma 0 1 ^ 2 - gamma 1 0 ^ 2 - gamma 1 1 ^ 2) / 2

private theorem buserSarnak_cosh_dist_smul_I (gamma : SL(2, ℝ)) (z : ℍ) :
    Real.cosh (dist (gamma • (I : ℍ)) z) =
      Internal.BuserSarnakHelpers.matrixHyperboloid0 gamma * Internal.BuserSarnakHelpers.hyperboloid0 z -
        Internal.BuserSarnakHelpers.matrixHyperboloid1 gamma * Internal.BuserSarnakHelpers.hyperboloid1 z -
          Internal.BuserSarnakHelpers.matrixHyperboloid2 gamma * Internal.BuserSarnakHelpers.hyperboloid2 z := by
  have hdet := gamma.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdet' : gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1 = 1 := by
    convert hdet using 1 <;> ring
  have hdetSq : (gamma 0 0 * gamma 1 1 - gamma 1 0 * gamma 0 1) ^ 2 = 1 := by
    rw [hdet']
    norm_num
  have hD : gamma 1 0 ^ 2 + gamma 1 1 ^ 2 ≠ 0 := by
    intro hzero
    have hc : gamma 1 0 = 0 := by nlinarith [sq_nonneg (gamma 1 1)]
    have hd : gamma 1 1 = 0 := by nlinarith [sq_nonneg (gamma 1 0)]
    rw [hc, hd] at hdet'
    norm_num at hdet'
  rw [UpperHalfPlane.cosh_dist', buserSarnak_re_smul_I, buserSarnak_im_smul_I]
  unfold Internal.BuserSarnakHelpers.matrixHyperboloid0 Internal.BuserSarnakHelpers.matrixHyperboloid1 Internal.BuserSarnakHelpers.matrixHyperboloid2
  unfold Internal.BuserSarnakHelpers.hyperboloid0 Internal.BuserSarnakHelpers.hyperboloid1 Internal.BuserSarnakHelpers.hyperboloid2
  field_simp [hD, z.im_ne_zero]
  nlinarith [hdetSq]

private theorem hyperboloid_linear_le_of_minimal
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z))
    (gamma : BuserSarnakQuaternionUnit.fullDeckGroup23) :
    Internal.BuserSarnakHelpers.matrixHyperboloid1 gamma * Internal.BuserSarnakHelpers.hyperboloid1 z +
        Internal.BuserSarnakHelpers.matrixHyperboloid2 gamma * Internal.BuserSarnakHelpers.hyperboloid2 z ≤
      (Internal.BuserSarnakHelpers.matrixHyperboloid0 gamma - 1) * Internal.BuserSarnakHelpers.hyperboloid0 z := by
  have hdist : dist (I : ℍ) z ≤ dist ((gamma : SL(2, ℝ)) • I) z := by
    calc
      dist (I : ℍ) z ≤ dist I (gamma⁻¹ • z) := hmin gamma⁻¹
      _ = dist ((gamma : SL(2, ℝ)) • I) z := by
        change dist (I : ℍ) ((gamma : SL(2, ℝ))⁻¹ • z) = _
        rw [← dist_smul (gamma : SL(2, ℝ)) (I : ℍ)
          (((gamma : SL(2, ℝ))⁻¹) • z)]
        simp [smul_smul]
  have hcosh : Real.cosh (dist (I : ℍ) z) ≤
      Real.cosh (dist ((gamma : SL(2, ℝ)) • I) z) := by
    rw [Real.cosh_le_cosh]
    simpa only [abs_of_nonneg dist_nonneg] using hdist
  rw [← hyperboloid0_eq_cosh_dist_I,
    buserSarnak_cosh_dist_smul_I] at hcosh
  linarith

def Internal.BuserSarnakHelpers.dirichletAPlus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨2, 0, 1, 0, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletAMinus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨2, 0, -1, 0, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletCPlus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨3, 2, 0, 0, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletCMinus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨3, -2, 0, 0, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletBPlusPlus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨0, -1, 1, 1, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletBPlusMinus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨0, -1, -1, 1, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletBMinusPlus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨0, 1, 1, 1, by norm_num⟩

def Internal.BuserSarnakHelpers.dirichletBMinusMinus : BuserSarnakQuaternionUnit 2 3 :=
  ⟨0, 1, -1, 1, by norm_num⟩

private theorem dirichlet_A_bounds_of_minimal
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z)) :
    4 * Real.sqrt 3 * Internal.BuserSarnakHelpers.hyperboloid1 z ≤ 6 * Internal.BuserSarnakHelpers.hyperboloid0 z ∧
      -(4 * Real.sqrt 3) * Internal.BuserSarnakHelpers.hyperboloid1 z ≤ 6 * Internal.BuserSarnakHelpers.hyperboloid0 z := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletAPlus)
  have hm := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletAMinus)
  norm_num [Internal.BuserSarnakHelpers.matrixHyperboloid0, Internal.BuserSarnakHelpers.matrixHyperboloid1, Internal.BuserSarnakHelpers.matrixHyperboloid2,
    BuserSarnakQuaternionUnit.toFullDeckGroup23,
    BuserSarnakQuaternionUnit.toSLHom, BuserSarnakQuaternionUnit.toSL,
    BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    Internal.BuserSarnakHelpers.dirichletAPlus, Internal.BuserSarnakHelpers.dirichletAMinus, hs2, hs3] at hp hm
  constructor
  · linarith
  · linarith

private theorem dirichlet_C_bounds_of_minimal
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z)) :
    12 * Real.sqrt 2 * Internal.BuserSarnakHelpers.hyperboloid2 z ≤ 16 * Internal.BuserSarnakHelpers.hyperboloid0 z ∧
      -(12 * Real.sqrt 2) * Internal.BuserSarnakHelpers.hyperboloid2 z ≤ 16 * Internal.BuserSarnakHelpers.hyperboloid0 z := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletCPlus)
  have hm := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletCMinus)
  norm_num [Internal.BuserSarnakHelpers.matrixHyperboloid0, Internal.BuserSarnakHelpers.matrixHyperboloid1, Internal.BuserSarnakHelpers.matrixHyperboloid2,
    BuserSarnakQuaternionUnit.toFullDeckGroup23,
    BuserSarnakQuaternionUnit.toSLHom, BuserSarnakQuaternionUnit.toSL,
    BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    Internal.BuserSarnakHelpers.dirichletCPlus, Internal.BuserSarnakHelpers.dirichletCMinus, hs2, hs3] at hp hm
  constructor
  · nlinarith [hs2]
  · nlinarith [hs2]

private theorem dirichlet_B_bounds_of_minimal
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z)) :
    4 * Real.sqrt 3 * Internal.BuserSarnakHelpers.hyperboloid1 z + 6 * Real.sqrt 2 * Internal.BuserSarnakHelpers.hyperboloid2 z ≤
        10 * Internal.BuserSarnakHelpers.hyperboloid0 z ∧
      4 * Real.sqrt 3 * Internal.BuserSarnakHelpers.hyperboloid1 z - 6 * Real.sqrt 2 * Internal.BuserSarnakHelpers.hyperboloid2 z ≤
        10 * Internal.BuserSarnakHelpers.hyperboloid0 z ∧
      -(4 * Real.sqrt 3) * Internal.BuserSarnakHelpers.hyperboloid1 z + 6 * Real.sqrt 2 * Internal.BuserSarnakHelpers.hyperboloid2 z ≤
        10 * Internal.BuserSarnakHelpers.hyperboloid0 z ∧
      -(4 * Real.sqrt 3) * Internal.BuserSarnakHelpers.hyperboloid1 z - 6 * Real.sqrt 2 * Internal.BuserSarnakHelpers.hyperboloid2 z ≤
        10 * Internal.BuserSarnakHelpers.hyperboloid0 z := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpp := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletBPlusPlus)
  have hpm := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletBPlusMinus)
  have hmp := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletBMinusPlus)
  have hmm := hyperboloid_linear_le_of_minimal z hmin
    (BuserSarnakQuaternionUnit.toFullDeckGroup23 Internal.BuserSarnakHelpers.dirichletBMinusMinus)
  norm_num [Internal.BuserSarnakHelpers.matrixHyperboloid0, Internal.BuserSarnakHelpers.matrixHyperboloid1, Internal.BuserSarnakHelpers.matrixHyperboloid2,
    BuserSarnakQuaternionUnit.toFullDeckGroup23,
    BuserSarnakQuaternionUnit.toSLHom, BuserSarnakQuaternionUnit.toSL,
    BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    Internal.BuserSarnakHelpers.dirichletBPlusPlus, Internal.BuserSarnakHelpers.dirichletBPlusMinus, Internal.BuserSarnakHelpers.dirichletBMinusPlus,
    Internal.BuserSarnakHelpers.dirichletBMinusMinus, hs2, hs3] at hpp hpm hmp hmm
  ring_nf at hpp hpm hmp hmm
  norm_num [hs2, hs3] at hpp hpm hmp hmm
  constructor
  · nlinarith [hs2, hs3]
  constructor
  · nlinarith [hs2, hs3]
  constructor <;> nlinarith [hs2, hs3]

private theorem dirichlet_octagon_sq_bound
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z)) :
    36 * (Internal.BuserSarnakHelpers.hyperboloid1 z ^ 2 + Internal.BuserSarnakHelpers.hyperboloid2 z ^ 2) ≤
      35 * Internal.BuserSarnakHelpers.hyperboloid0 z ^ 2 := by
  let T := Internal.BuserSarnakHelpers.hyperboloid0 z
  let U := Internal.BuserSarnakHelpers.hyperboloid1 z
  let V := Internal.BuserSarnakHelpers.hyperboloid2 z
  let A := |U|
  let B := |V|
  have hT : 0 < T := hyperboloid0_pos z
  have hA0 : 0 ≤ A := abs_nonneg U
  have hB0 : 0 ≤ B := abs_nonneg V
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨hUp, hUm⟩ := dirichlet_A_bounds_of_minimal z hmin
  obtain ⟨hVp, hVm⟩ := dirichlet_C_bounds_of_minimal z hmin
  obtain ⟨hPP, hPM, hMP, hMM⟩ := dirichlet_B_bounds_of_minimal z hmin
  change 4 * Real.sqrt 3 * U ≤ 6 * T at hUp
  change -(4 * Real.sqrt 3) * U ≤ 6 * T at hUm
  change 12 * Real.sqrt 2 * V ≤ 16 * T at hVp
  change -(12 * Real.sqrt 2) * V ≤ 16 * T at hVm
  change 4 * Real.sqrt 3 * U + 6 * Real.sqrt 2 * V ≤ 10 * T at hPP
  change 4 * Real.sqrt 3 * U - 6 * Real.sqrt 2 * V ≤ 10 * T at hPM
  change -(4 * Real.sqrt 3) * U + 6 * Real.sqrt 2 * V ≤ 10 * T at hMP
  change -(4 * Real.sqrt 3) * U - 6 * Real.sqrt 2 * V ≤ 10 * T at hMM
  have hUscaled : |4 * Real.sqrt 3 * U| ≤ 6 * T :=
    abs_le.mpr ⟨by linarith, hUp⟩
  have hVscaled : |12 * Real.sqrt 2 * V| ≤ 16 * T :=
    abs_le.mpr ⟨by linarith, hVp⟩
  have hUabs : 4 * Real.sqrt 3 * A ≤ 6 * T := by
    simpa [A, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 3)] using hUscaled
  have hVabs : 12 * Real.sqrt 2 * B ≤ 16 * T := by
    simpa [B, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)] using hVscaled
  have hdiag : 4 * Real.sqrt 3 * A + 6 * Real.sqrt 2 * B ≤ 10 * T := by
    by_cases hU : 0 ≤ U
    · simp only [A, abs_of_nonneg hU]
      by_cases hV : 0 ≤ V
      · simp only [B, abs_of_nonneg hV]
        exact hPP
      · have hV' : V ≤ 0 := le_of_not_ge hV
        simp only [B, abs_of_nonpos hV']
        nlinarith [hPM]
    · have hU' : U ≤ 0 := le_of_not_ge hU
      simp only [A, abs_of_nonpos hU']
      by_cases hV : 0 ≤ V
      · simp only [B, abs_of_nonneg hV]
        nlinarith [hMP]
      · have hV' : V ≤ 0 := le_of_not_ge hV
        simp only [B, abs_of_nonpos hV']
        nlinarith [hMM]
  have hsquare : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → x ^ 2 ≤ y ^ 2 := by
    intro x y hx hxy
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx (hx.trans hxy))]
  have hAupper : 2 * A ≤ Real.sqrt 3 * T := by
    by_contra hnot
    have hlt : Real.sqrt 3 * T < 2 * A := lt_of_not_ge hnot
    have htwoR3 : 0 < 2 * Real.sqrt 3 := mul_pos (by norm_num) hr3
    have hmul := mul_lt_mul_of_pos_left hlt htwoR3
    nlinarith [hs3, hUabs]
  by_cases hAlow : 6 * A ≤ Real.sqrt 3 * T
  · have hAsq := hsquare (mul_nonneg (by norm_num) hA0) hAlow
    have hVsq := hsquare
      (mul_nonneg (mul_nonneg (by norm_num) hr2.le) hB0) hVabs
    change 36 * (U ^ 2 + V ^ 2) ≤ 35 * T ^ 2
    dsimp [A, B] at hAsq hVsq
    nlinarith [hs2, hs3, sq_abs U, sq_abs V]
  · have hAlow' : Real.sqrt 3 * T ≤ 6 * A := le_of_not_ge hAlow
    have hfactor :
        (6 * A - Real.sqrt 3 * T) * (2 * A - Real.sqrt 3 * T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hAlow')
        (sub_nonpos.mpr hAupper)
    have hdiag' : 6 * Real.sqrt 2 * B ≤
        10 * T - 4 * Real.sqrt 3 * A := by
      linarith
    have hdiagSq := hsquare
      (mul_nonneg (mul_nonneg (by norm_num) hr2.le) hB0) hdiag'
    change 36 * (U ^ 2 + V ^ 2) ≤ 35 * T ^ 2
    dsimp [A, B] at hfactor hdiagSq
    nlinarith [hs2, hs3, sq_abs U, sq_abs V]

private theorem hyperboloid0_le_six_of_minimal
    (z : ℍ) (hmin : ∀ gamma : BuserSarnakQuaternionUnit.fullDeckGroup23,
      dist (I : ℍ) z ≤ dist I (gamma • z)) :
    Internal.BuserSarnakHelpers.hyperboloid0 z ≤ 6 := by
  have hsq := dirichlet_octagon_sq_bound z hmin
  have hidentity := hyperboloid0_sq_sub_sq_sub_sq z
  have hpos := hyperboloid0_pos z
  nlinarith

/-- A concrete compact orbit-covering set for the full `(2,3)` arithmetic
group.  It contains the Dirichlet octagon centered at `I`. -/
noncomputable def BuserSarnakQuaternionUnit.fullFundamentalSet23 : Set ℍ :=
  Metric.closedBall (I : ℍ) (Real.arcosh 6)

theorem BuserSarnakQuaternionUnit.fullFundamentalSet23_isCompact :
    IsCompact fullFundamentalSet23 :=
  isCompact_closedBall (I : ℍ) (Real.arcosh 6)

theorem BuserSarnakQuaternionUnit.fullFundamentalSet23_orbit_cover
    (z : ℍ) : ∃ gamma : fullDeckGroup23, gamma • z ∈ fullFundamentalSet23 := by
  letI : DiscreteTopology fullDeckGroup23 :=
    isDiscrete_iff_discreteTopology.mp fullDeckGroup23_isDiscrete
  obtain ⟨gamma, hgamma⟩ :=
    exists_smul_minimizing_distance (G := fullDeckGroup23) (I : ℍ) z
  let w : ℍ := gamma • z
  have hwmin : ∀ eta : fullDeckGroup23,
      dist (I : ℍ) w ≤ dist I (eta • w) := by
    intro eta
    simpa [w, mul_smul] using hgamma (eta * gamma)
  have hcosh : Real.cosh (dist (I : ℍ) w) ≤ 6 := by
    rw [← hyperboloid0_eq_cosh_dist_I]
    exact hyperboloid0_le_six_of_minimal w hwmin
  have hdist : dist (I : ℍ) w ≤ Real.arcosh 6 := by
    rw [← Real.arcosh_cosh dist_nonneg]
    exact (Real.arcosh_le_arcosh (Real.cosh_pos _) (by norm_num)).mpr hcosh
  refine ⟨gamma, ?_⟩
  change w ∈ Metric.closedBall (I : ℍ) (Real.arcosh 6)
  exact Metric.mem_closedBall.mpr (by simpa [dist_comm] using hdist)

theorem BuserSarnakQuaternionUnit.fullDeckGroup23_compactQuotient :
    IsCompact (Set.univ : Set
      (MulAction.orbitRel.Quotient fullDeckGroup23 ℍ)) :=
  isCompact_orbitRel_quotient_of_compact_cover fullFundamentalSet23
    fullFundamentalSet23_isCompact fullFundamentalSet23_orbit_cover

/-- Unconditional cocompactness of every nonzero principal level in the
concrete Buser--Sarnak family. -/
theorem BuserSarnakQuaternionUnit.levelDeckGroup23_compactQuotient
    (p : ℕ) [NeZero p] :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient
      (levelDeckGroup (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)) ℍ)) :=
  levelDeckGroup23_compactQuotient_of_full_compact_cover fullFundamentalSet23
    fullFundamentalSet23_isCompact fullFundamentalSet23_orbit_cover p

private theorem buserSarnak_abs_trace_le_two_cosh_half_at_I (gamma : SL(2, ℝ)) :
    |(gamma : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤
      2 * Real.cosh (dist (I : ℍ) (gamma • I) / 2) := by
  have hdet := gamma.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hcosh := buserSarnak_cosh_smul_I gamma
  have hcosh_two : Real.cosh (dist (I : ℍ) (gamma • I)) =
      2 * Real.cosh (dist (I : ℍ) (gamma • I) / 2) ^ 2 - 1 := by
    calc
      Real.cosh (dist (I : ℍ) (gamma • I)) =
          Real.cosh (2 * (dist (I : ℍ) (gamma • I) / 2)) := by congr 1 <;> ring
      _ = Real.cosh (dist (I : ℍ) (gamma • I) / 2) ^ 2 +
          Real.sinh (dist (I : ℍ) (gamma • I) / 2) ^ 2 := Real.cosh_two_mul _
      _ = 2 * Real.cosh (dist (I : ℍ) (gamma • I) / 2) ^ 2 - 1 := by
        nlinarith [Real.cosh_sq (dist (I : ℍ) (gamma • I) / 2)]
  have htrace_sq : (gamma 0 0 + gamma 1 1) ^ 2 ≤
      (2 * Real.cosh (dist (I : ℍ) (gamma • I) / 2)) ^ 2 := by
    nlinarith [hcosh, hcosh_two, sq_nonneg (gamma 0 1 - gamma 1 0)]
  have habs : |gamma 0 0 + gamma 1 1| ≤
      |2 * Real.cosh (dist (I : ℍ) (gamma • I) / 2)| := (sq_le_sq).mp htrace_sq
  simpa [Matrix.trace, Fin.sum_univ_two, abs_of_pos (Real.cosh_pos _)] using habs

private theorem buserSarnak_trace_conj (h gamma : SL(2, ℝ)) :
    ((h⁻¹ * gamma * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      (gamma : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  calc
    ((h⁻¹ * gamma * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
        (((h⁻¹ * gamma : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)).trace := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
    _ = (((h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((h⁻¹ * gamma : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((h * (h⁻¹ * gamma) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
      symm
      exact congrArg Matrix.trace (Matrix.SpecialLinearGroup.coe_mul h (h⁻¹ * gamma))
    _ = (gamma : Matrix (Fin 2) (Fin 2) ℝ).trace := by simp

private theorem buserSarnak_distance_conj (z : ℍ) (gamma : SL(2, ℝ)) :
    dist (I : ℍ) ((z.toSL2R⁻¹ * gamma * z.toSL2R) • I) =
      dist z (gamma • z) := by
  let h := z.toSL2R
  calc
    dist (I : ℍ) ((h⁻¹ * gamma * h) • I) =
        dist (h • I) (h • ((h⁻¹ * gamma * h) • I) ) := (dist_smul h _ _).symm
    _ = dist z (gamma • z) := by
      simp [h, mul_smul, UpperHalfPlane.toSL2R_smul_I]

theorem abs_trace_le_two_cosh_half_displacement (gamma : SL(2, ℝ)) (z : ℍ) :
    |(gamma : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤
      2 * Real.cosh (dist z (gamma • z) / 2) := by
  let h := z.toSL2R
  have hbase := buserSarnak_abs_trace_le_two_cosh_half_at_I (h⁻¹ * gamma * h)
  rw [buserSarnak_trace_conj h gamma, buserSarnak_distance_conj z gamma] at hbase
  exact hbase

theorem displacement_lower_of_abs_trace_lower_bound
    (p : ℕ) (hp : p.Prime) (z : ℍ) (gamma : SL(2, ℝ))
    (htrace : 2 * (p : ℝ) ^ 2 - 2 ≤
      |(gamma : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    4 * Real.log (p : ℝ) ≤ dist z (gamma • z) := by
  let x : ℝ := dist z (gamma • z) / 2
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hnegexp : Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcosh : 2 * Real.cosh x ≤ Real.exp x + 1 := by
    rw [Real.cosh_eq]
    nlinarith
  have hcombined : 2 * (p : ℝ) ^ 2 - 2 ≤ 2 * Real.cosh x := by
    exact htrace.trans (by simpa [x] using abs_trace_le_two_cosh_half_displacement gamma z)
  have hexp_lower : 2 * (p : ℝ) ^ 2 - 3 ≤ Real.exp x := by
    nlinarith
  have hp_two : (2 : ℝ) ≤ p := by
    exact_mod_cast hp.two_le
  have hp_sq : (p : ℝ) ^ 2 ≤ 2 * (p : ℝ) ^ 2 - 3 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hp_exp : (p : ℝ) ^ 2 ≤ Real.exp x := hp_sq.trans hexp_lower
  have hp_pos : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by positivity)
  have hlog : Real.log ((p : ℝ) ^ 2) ≤ x :=
    (Real.log_le_iff_le_exp hp_pos).mpr hp_exp
  calc
    4 * Real.log (p : ℝ) = 2 * Real.log ((p : ℝ) ^ 2) := by
      rw [Real.log_pow]
      norm_num
      ring
    _ ≤ 2 * x := by nlinarith
    _ = dist z (gamma • z) := by
      dsimp [x]
      ring

theorem BuserSarnakQuaternionUnit.nontrivial_levelDeckGroup_displacement_lower23
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    (gamma : BuserSarnakQuaternionUnit.levelDeckGroup
      (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ))
    (hgamma : gamma ≠ 1) (z : ℍ) :
    4 * Real.log (p : ℝ) ≤ dist z (gamma • z) := by
  apply displacement_lower_of_abs_trace_lower_bound p hp z gamma
  apply BuserSarnakQuaternionUnit.nontrivial_levelDeckGroup_real_abs_trace_lower_bound23
    hp hp_two gamma.property
  intro hgamma_coe
  apply hgamma
  apply Subtype.ext
  exact hgamma_coe

theorem BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_eq
    {g p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    (X : SystolicGrowth.ClosedHyperbolicSurface g)
    (hdeck : X.deckGroup = BuserSarnakQuaternionUnit.levelDeckGroup
      (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ))
    (hnonempty : X.translationLengths.Nonempty) :
    4 * Real.log (p : ℝ) ≤ X.systole := by
  apply SystolicGrowth.ClosedHyperbolicSurface.le_systole_of_displacement_lower
    X _ hnonempty
  intro gamma hgamma z
  change 4 * Real.log (p : ℝ) ≤ dist z ((gamma : SL(2, ℝ)) • z)
  have hmem : (gamma : SL(2, ℝ)) ∈ BuserSarnakQuaternionUnit.levelDeckGroup
      (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ) := by
    rw [← hdeck]
    exact gamma.property
  apply displacement_lower_of_abs_trace_lower_bound p hp z gamma
  apply BuserSarnakQuaternionUnit.nontrivial_levelDeckGroup_real_abs_trace_lower_bound23
    hp hp_two hmem
  intro hgamma_coe
  apply hgamma
  apply Subtype.ext
  exact hgamma_coe

theorem BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_eq_of_genus_pos
    {g p : ℕ} (hg : 0 < g) (hp : p.Prime) (hp_two : p ≠ 2)
    (X : SystolicGrowth.ClosedHyperbolicSurface g)
    (hdeck : X.deckGroup = BuserSarnakQuaternionUnit.levelDeckGroup
      (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)) :
    4 * Real.log (p : ℝ) ≤ X.systole :=
  BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_eq hp hp_two X hdeck
    (SystolicGrowth.ClosedHyperbolicSurface.translationLengths_nonempty_of_genus_pos X hg)

theorem BuserSarnakQuaternionUnit.levelDeckGroup_free23
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) :
    ∀ gamma : levelDeckGroup (a := 2) (b := 3)
      (by norm_num) (by norm_num) (p : ℤ),
    ∀ z : ℍ, gamma • z = z → gamma = 1 := by
  intro gamma z hfix
  by_contra hgamma_ne_one
  have hgamma_coe_ne_one : (gamma : SL(2, ℝ)) ≠ 1 := by
    intro hcoe
    apply hgamma_ne_one
    apply Subtype.ext
    exact hcoe
  have hlower := nontrivial_levelDeckGroup_real_abs_trace_lower_bound23
    hp hp_two gamma.property hgamma_coe_ne_one
  have hupper : |((gamma : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤ 2 :=
    abs_trace_le_two_of_fixed_point (gamma : SL(2, ℝ)) z hfix
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_three : 3 ≤ p := by omega
  have hp_three_real : (3 : ℝ) ≤ p := by exact_mod_cast hp_three
  have htoo_large : 2 < 2 * (p : ℝ) ^ 2 - 2 := by nlinarith
  exact (not_le_of_gt htoo_large) (hlower.trans hupper)

end SystolicGrowth
