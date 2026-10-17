module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalLargePrimeLift
public import CookMagyar.FiniteMultiplicativity

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Exact counts of nonsingular prime-power lifts

The one-step lifting theorem is refined here to count its full fiber.  The
key finite-linear fact is that one nonzero coefficient lets us eliminate
one correction digit, leaving `p^(n-1)` free digits.
-/

/-- An affine hyperplane in the finite coordinate space `(Fin n → ZMod p)`. -/
abbrev AffineDigitHyperplane (p n : ℕ) (coeff : Fin n → ZMod p)
    (rhs : ZMod p) :=
  {y : Fin n → ZMod p // ∑ i, coeff i * y i = rhs}

/-- Restrict a digit tuple to all coordinates other than `j`. -/
def eraseDigitCoordinate {p n : ℕ} (j : Fin n) (y : Fin n → ZMod p) :
    {i : Fin n // i ≠ j} → ZMod p := fun i ↦ y i

/-- A finite affine hyperplane with a nonzero `j`-coefficient is equivalent
to the unrestricted digits away from `j`. -/
noncomputable def affineDigitHyperplaneEquiv {p n : ℕ} (hp : p.Prime)
    (coeff : Fin n → ZMod p) (rhs : ZMod p) (j : Fin n)
    (hj : coeff j ≠ 0) :
    AffineDigitHyperplane p n coeff rhs ≃
      ({i : Fin n // i ≠ j} → ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  let restrict : AffineDigitHyperplane p n coeff rhs →
      ({i : Fin n // i ≠ j} → ZMod p) :=
    fun y ↦ eraseDigitCoordinate j y
  apply Equiv.ofBijective restrict
  constructor
  · intro y z hyz
    apply Subtype.ext
    funext i
    by_cases hi : i = j
    · subst i
      have hoff :
          ∑ a ∈ (Finset.univ : Finset (Fin n)).erase j, coeff a * y.1 a =
            ∑ a ∈ (Finset.univ : Finset (Fin n)).erase j, coeff a * z.1 a := by
        apply Finset.sum_congr rfl
        intro a ha
        have haj : a ≠ j := (Finset.mem_erase.mp ha).1
        have hvalue := congrFun hyz ⟨a, haj⟩
        exact congrArg (coeff a * ·) hvalue
      have hy := y.2
      have hz := z.2
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hy hz
      rw [hoff] at hy
      have hmul : coeff j * y.1 j = coeff j * z.1 j :=
        add_left_cancel (hy.trans hz.symm)
      exact (mul_left_cancel₀ hj) hmul
    · exact congrFun hyz ⟨i, hi⟩
  · intro z
    let zFull : Fin n → ZMod p := fun i ↦
      if hi : i ≠ j then z ⟨i, hi⟩ else 0
    let tail : ZMod p :=
      ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
        coeff i * zFull i
    let y : Fin n → ZMod p := fun i ↦
      if hi : i = j then (coeff j)⁻¹ * (rhs - tail) else z ⟨i, hi⟩
    have hy_off (i : Fin n) (hi : i ≠ j) : y i = z ⟨i, hi⟩ := by
      simp [y, hi]
    have htail :
        ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, coeff i * y i = tail := by
      unfold tail
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      rw [hy_off i hij]
      simp [zFull, hij]
    have hy_equation : ∑ i, coeff i * y i = rhs := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), htail]
      simp only [y]
      simp [hj]
    refine ⟨⟨y, hy_equation⟩, ?_⟩
    funext i
    exact hy_off i i.2

/-- Exact cardinality of a nonsingular affine digit hyperplane. -/
theorem card_affineDigitHyperplane {p n : ℕ} (hp : p.Prime)
    [NeZero p]
    (coeff : Fin n → ZMod p) (rhs : ZMod p) (j : Fin n)
    (hj : coeff j ≠ 0) :
    Fintype.card (AffineDigitHyperplane p n coeff rhs) = p ^ (n - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  calc
    Fintype.card (AffineDigitHyperplane p n coeff rhs) =
        Fintype.card ({i : Fin n // i ≠ j} → ZMod p) :=
      Fintype.card_congr (affineDigitHyperplaneEquiv hp coeff rhs j hj)
    _ = p ^ (n - 1) := by
      have hcard : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
        simpa using Set.card_ne_eq j
      rw [Fintype.card_fun, ZMod.card, hcard]

/-! ## Digit coordinates on a one-step lift fiber -/

/-- Apply one correction digit independently in every coordinate. -/
def digitTupleLift (p k : ℕ) [NeZero p] {n : ℕ}
    (x : Fin n → ZMod (p ^ (k + 1))) (y : Fin n → ZMod p) :
    Fin n → ZMod (p ^ (k + 1)) := fun i ↦
  x i + (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k (y i)

/-- The finite type of all coordinatewise lifts of a fixed tuple. -/
abbrev CoordinateLiftFiber (p k n : ℕ) [NeZero p]
    (base : Fin n → ZMod (p ^ k)) :=
  {z : Fin n → ZMod (p ^ (k + 1)) //
    ∀ i, primePowerReduction p k (z i) = base i}

/-- Digit tuples parametrize the complete coordinatewise reduction fiber. -/
noncomputable def digitTupleLiftFiberEquiv (p k n : ℕ) [NeZero p]
    (base : Fin n → ZMod (p ^ k))
    (x : Fin n → ZMod (p ^ (k + 1)))
    (hx : ∀ i, primePowerReduction p k (x i) = base i) :
    (Fin n → ZMod p) ≃ CoordinateLiftFiber p k n base := by
  let lift : (Fin n → ZMod p) → CoordinateLiftFiber p k n base := fun y ↦
    ⟨digitTupleLift p k x y, fun i ↦ by
      rw [digitTupleLift, primePowerReduction_add_digit, hx]⟩
  apply Equiv.ofBijective lift
  constructor
  · intro y z hyz
    funext i
    apply primePowerDigit_mul_injective p k
    have hi := congrArg (fun w ↦ w.1 i) hyz
    exact add_left_cancel hi
  · rintro ⟨z, hz⟩
    have hzero (i : Fin n) :
        primePowerReduction p k (z i - x i) = 0 := by
      rw [map_sub, hz, hx, sub_self]
    choose y hy using fun i ↦
      exists_primePowerDigit_of_reduction_eq_zero p k (z i - x i) (hzero i)
    refine ⟨y, Subtype.ext ?_⟩
    funext i
    change x i + (p ^ k : ZMod (p ^ (k + 1))) *
        primePowerDigit p k (y i) = z i
    rw [← hy i]
    abel

/-- Casting the standard representative of a digit back modulo `p`
recovers that digit. -/
@[simp] theorem cast_primePowerDigit (p k : ℕ) [NeZero p] (a : ZMod p) :
    ((primePowerDigit p k a).cast : ZMod p) = a := by
  have hdiv : p ∣ p ^ (k + 1) := by
    simp [pow_succ]
  unfold primePowerDigit
  rw [ZMod.cast_natCast hdiv, ZMod.natCast_zmod_val]

/-- Exact summation of the coordinatewise Taylor formulas. -/
theorem cubicResidue_sum_digitTupleLift (p k : ℕ) [NeZero p]
    (hk : 1 ≤ k) {n : ℕ} (x : Fin n → ZMod (p ^ (k + 1)))
    (y : Fin n → ZMod p) :
    ∑ i, cubicResidue (digitTupleLift p k x y i) =
      (∑ i, cubicResidue (x i)) +
        (p ^ k : ZMod (p ^ (k + 1))) *
          ∑ i, primePowerDigit p k (y i) * cubicDerivative (x i) := by
  simp_rw [digitTupleLift, cubicResidue_add_primePower_mul p k hk]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- After multiplication by `p^k`, a lifted linear form is represented by
the same linear form in the correction digits modulo `p`. -/
theorem primePower_mul_digitLinearForm (p k : ℕ) [NeZero p]
    {n : ℕ} (x : Fin n → ZMod (p ^ (k + 1))) (y : Fin n → ZMod p) :
    (p ^ k : ZMod (p ^ (k + 1))) *
        (∑ i, primePowerDigit p k (y i) * cubicDerivative (x i)) =
      (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k
        (∑ i, (cubicDerivative (x i)).cast * y i) := by
  apply primePower_mul_eq_of_cast_eq p k
  have hdiv : p ∣ p ^ (k + 1) := by
    simp [pow_succ]
  let castP := ZMod.castHom hdiv (ZMod p)
  change castP (∑ i, primePowerDigit p k (y i) * cubicDerivative (x i)) = _
  rw [map_sum, cast_primePowerDigit]
  simp only [map_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  change ((primePowerDigit p k (y i)).cast : ZMod p) *
      ((cubicDerivative (x i)).cast : ZMod p) = _
  rw [cast_primePowerDigit]
  exact mul_comm (y i) ((cubicDerivative (x i)).cast : ZMod p)

/-! ## The equation cuts out one affine digit hyperplane -/

/-- The unique base-`p` digit represented by an error killed by reduction. -/
noncomputable def liftErrorDigit (p k : ℕ) [NeZero p]
    (e : ZMod (p ^ (k + 1))) (he : primePowerReduction p k e = 0) :
    ZMod p :=
  (primePowerKernelEquiv p k).symm ⟨e, he⟩

/-- The defining property of the error digit. -/
theorem primePower_mul_liftErrorDigit (p k : ℕ) [NeZero p]
    (e : ZMod (p ^ (k + 1))) (he : primePowerReduction p k e = 0) :
    (p ^ k : ZMod (p ^ (k + 1))) *
        primePowerDigit p k (liftErrorDigit p k e he) = e := by
  have h := (primePowerKernelEquiv p k).apply_symm_apply ⟨e, he⟩
  exact congrArg Subtype.val h

/-- A corrected tuple solves the next-level equation exactly when its
digits satisfy one affine linear equation modulo `p`. -/
theorem digitTupleLift_equation_iff (p k : ℕ) [NeZero p]
    (hk : 1 ≤ k) {n : ℕ} (x : Fin n → ZMod (p ^ (k + 1)))
    (T : ZMod (p ^ (k + 1)))
    (herror : primePowerReduction p k
      (T - ∑ i, cubicResidue (x i)) = 0)
    (y : Fin n → ZMod p) :
    (∑ i, cubicResidue (digitTupleLift p k x y i) = T) ↔
      (∑ i, (cubicDerivative (x i)).cast * y i =
        liftErrorDigit p k (T - ∑ i, cubicResidue (x i)) herror) := by
  let linear : ZMod p := ∑ i, (cubicDerivative (x i)).cast * y i
  let rhs : ZMod p :=
    liftErrorDigit p k (T - ∑ i, cubicResidue (x i)) herror
  have hlinear :
      (p ^ k : ZMod (p ^ (k + 1))) *
          (∑ i, primePowerDigit p k (y i) * cubicDerivative (x i)) =
        (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k linear := by
    exact primePower_mul_digitLinearForm p k x y
  have hrhs :
      (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k rhs =
        T - ∑ i, cubicResidue (x i) := by
    exact primePower_mul_liftErrorDigit p k _ herror
  rw [cubicResidue_sum_digitTupleLift p k hk, hlinear]
  change ((∑ i, cubicResidue (x i)) +
      (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k linear = T) ↔
        linear = rhs
  constructor
  · intro hequation
    apply primePowerDigit_mul_injective p k
    change (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k linear =
      (p ^ k : ZMod (p ^ (k + 1))) * primePowerDigit p k rhs
    rw [hrhs]
    linear_combination hequation
  · intro hlinear_rhs
    rw [hlinear_rhs, hrhs]
    ring

/-- The solution lifts of a fixed tuple, represented as a subtype of its
coordinatewise reduction fiber. -/
abbrev CubicSolutionLiftFiber (p k n : ℕ) [NeZero p]
    (base : Fin n → ZMod (p ^ k)) (T : ZMod (p ^ (k + 1))) :=
  {z : CoordinateLiftFiber p k n base //
    ∑ i, cubicResidue (z.1 i) = T}

/-- The complete solution-lift fiber is equivalent to the free correction
digits away from any coordinate whose reduced derivative is nonzero. -/
noncomputable def cubicSolutionLiftFiberEquiv {p k n : ℕ} [NeZero p]
    (hp : p.Prime) (hk : 1 ≤ k)
    (base : Fin n → ZMod (p ^ k))
    (x : Fin n → ZMod (p ^ (k + 1)))
    (hx : ∀ i, primePowerReduction p k (x i) = base i)
    (T : ZMod (p ^ (k + 1)))
    (herror : primePowerReduction p k
      (T - ∑ i, cubicResidue (x i)) = 0)
    (j : Fin n) (hj : ((cubicDerivative (x j)).cast : ZMod p) ≠ 0) :
    CubicSolutionLiftFiber p k n base T ≃
      ({i : Fin n // i ≠ j} → ZMod p) := by
  let coordinateEquiv := digitTupleLiftFiberEquiv p k n base x hx
  let equationEquiv :
      AffineDigitHyperplane p n (fun i ↦ (cubicDerivative (x i)).cast)
          (liftErrorDigit p k (T - ∑ i, cubicResidue (x i)) herror) ≃
        CubicSolutionLiftFiber p k n base T :=
    coordinateEquiv.subtypeEquiv (fun y ↦ by
      have hcoordinate : (coordinateEquiv y).1 = digitTupleLift p k x y := rfl
      rw [hcoordinate]
      exact (digitTupleLift_equation_iff p k hk x T herror y).symm)
  exact equationEquiv.symm.trans
    (affineDigitHyperplaneEquiv hp
      (fun i ↦ (cubicDerivative (x i)).cast)
      (liftErrorDigit p k (T - ∑ i, cubicResidue (x i)) herror) j hj)

/-- Exact cardinality of a nonsingular one-step solution-lift fiber. -/
theorem card_cubicSolutionLiftFiber {p k n : ℕ} [NeZero p]
    (hp : p.Prime) (hk : 1 ≤ k)
    (base : Fin n → ZMod (p ^ k))
    (x : Fin n → ZMod (p ^ (k + 1)))
    (hx : ∀ i, primePowerReduction p k (x i) = base i)
    (T : ZMod (p ^ (k + 1)))
    (herror : primePowerReduction p k
      (T - ∑ i, cubicResidue (x i)) = 0)
    (j : Fin n) (hj : ((cubicDerivative (x j)).cast : ZMod p) ≠ 0) :
    Fintype.card (CubicSolutionLiftFiber p k n base T) = p ^ (n - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  calc
    Fintype.card (CubicSolutionLiftFiber p k n base T) =
        Fintype.card ({i : Fin n // i ≠ j} → ZMod p) :=
      Fintype.card_congr
        (cubicSolutionLiftFiberEquiv hp hk base x hx T herror j hj)
    _ = p ^ (n - 1) := by
      have hcard : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
        simpa using Set.card_ne_eq j
      rw [Fintype.card_fun, ZMod.card, hcard]

/-- Core.Reduction commutes with the cubic derivative. -/
theorem primePowerReduction_cubicDerivative (p k : ℕ) [NeZero p]
    (x : ZMod (p ^ (k + 1))) :
    primePowerReduction p k (cubicDerivative x) =
      cubicDerivative (primePowerReduction p k x) := by
  have hthree : primePowerReduction p k
      (3 : ZMod (p ^ (k + 1))) = (3 : ZMod (p ^ k)) :=
    map_ofNat (primePowerReduction p k) 3
  unfold cubicDerivative
  rw [map_sub, map_mul, map_pow, hthree, map_one]

/-- Choose a coordinatewise origin in any reduction fiber. -/
noncomputable def coordinateLiftOrigin (p k : ℕ) [NeZero p] {n : ℕ}
    (base : Fin n → ZMod (p ^ k)) : Fin n → ZMod (p ^ (k + 1)) :=
  fun i ↦ Classical.choose
    (ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ k)) (base i))

@[simp] theorem coordinateLiftOrigin_spec (p k : ℕ) [NeZero p] {n : ℕ}
    (base : Fin n → ZMod (p ^ k)) (i : Fin n) :
    primePowerReduction p k (coordinateLiftOrigin p k base i) = base i := by
  exact Classical.choose_spec
    (ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ k)) (base i))

/-- The target error of a lifted base solution lies in the reduction
kernel. -/
theorem solutionLift_error_reduction {p k n : ℕ} [NeZero p]
    {t : ZMod (p ^ k)} (base : Fin n → ZMod (p ^ k))
    (hbase : ∑ i, cubicResidue (base i) = t)
    (x : Fin n → ZMod (p ^ (k + 1)))
    (hx : ∀ i, primePowerReduction p k (x i) = base i)
    (T : ZMod (p ^ (k + 1))) (hT : primePowerReduction p k T = t) :
    primePowerReduction p k (T - ∑ i, cubicResidue (x i)) = 0 := by
  rw [map_sub, map_sum, hT]
  simp_rw [show ∀ i, primePowerReduction p k (cubicResidue (x i)) =
      cubicResidue (base i) by
    intro i
    simp [cubicResidue, hx]]
  rw [hbase, sub_self]

/-- A unit derivative at the base remains a nonzero derivative digit for
every chosen origin in the next-level reduction fiber. -/
theorem cast_cubicDerivative_ne_zero_of_reduction_isUnit
    {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : 1 ≤ k)
    (x : ZMod (p ^ (k + 1)))
    (hx : IsUnit (cubicDerivative (primePowerReduction p k x))) :
    ((cubicDerivative x).cast : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnext : IsUnit (cubicDerivative x) := by
    apply isUnit_of_primePowerReduction_isUnit p k hk
    simpa [primePowerReduction_cubicDerivative] using hx
  have hdiv : p ∣ p ^ (k + 1) := by simp [pow_succ]
  have hcast : IsUnit ((cubicDerivative x).cast : ZMod p) := by
    exact hnext.map (ZMod.castHom hdiv (ZMod p))
  exact hcast.ne_zero

/-- For a fixed nonsingular unit base solution and a chosen unit
derivative coordinate, the exact one-step solution fiber has `p^(n-1)`
elements. -/
theorem card_nonsingularUnitSolution_lift_fiber
    {p k n : ℕ} [NeZero p] (hp : p.Prime) (hk : 1 ≤ k)
    {t : ZMod (p ^ k)} (s : NonsingularUnitSolution (p ^ k) n t)
    (j : Fin n) (hj : IsUnit (cubicDerivative (s.point j)))
    (T : ZMod (p ^ (k + 1))) (hT : primePowerReduction p k T = t) :
    Fintype.card (CubicSolutionLiftFiber p k n s.point T) = p ^ (n - 1) := by
  let x := coordinateLiftOrigin p k s.point
  have hx : ∀ i, primePowerReduction p k (x i) = s.point i :=
    coordinateLiftOrigin_spec p k s.point
  have herror := solutionLift_error_reduction s.point s.equation x hx T hT
  apply card_cubicSolutionLiftFiber hp hk s.point x hx T herror j
  apply cast_cubicDerivative_ne_zero_of_reduction_isUnit hp hk
  simpa [hx] using hj

/-! ## Iterating the exact lift count -/

/-- Unit solutions for which one fixed partial derivative is a unit.  Fixing
the coordinate makes this class stable under reduction and lifting. -/
abbrev DistinguishedUnitSolution (q n : ℕ)
    (t : ZMod q) (j : Fin n) :=
  {x : Fin n → ZMod q //
    (∀ i, IsUnit (x i)) ∧
      (∑ i, cubicResidue (x i) = t) ∧
        IsUnit (cubicDerivative (x j))}

/-- Forgetting the distinguished coordinate gives the existing
nonsingular-solution structure. -/
def distinguishedToNonsingular {q n : ℕ} [NeZero q]
    {t : ZMod q} {j : Fin n} (hq : 1 < q)
    (s : DistinguishedUnitSolution q n t j) :
    NonsingularUnitSolution q n t := by
  letI : Fact (1 < q) := ⟨hq⟩
  exact {
    point := s.1
    isUnit_point := s.2.1
    equation := s.2.2.1
    nonsingular := ⟨j, s.2.2.2.ne_zero⟩
  }

/-- Reduce a distinguished solution by one prime-power level. -/
def reduceDistinguishedUnitSolution {p k n : ℕ} [NeZero p]
    {t : ZMod (p ^ k)} (T : ZMod (p ^ (k + 1)))
    (hT : primePowerReduction p k T = t) (j : Fin n)
    (s : DistinguishedUnitSolution (p ^ (k + 1)) n T j) :
    DistinguishedUnitSolution (p ^ k) n t j := by
  refine ⟨fun i ↦ primePowerReduction p k (s.1 i), ?_, ?_, ?_⟩
  · intro i
    exact (s.2.1 i).map (primePowerReduction p k)
  · calc
      (∑ i, cubicResidue (primePowerReduction p k (s.1 i))) =
          primePowerReduction p k (∑ i, cubicResidue (s.1 i)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [cubicResidue]
      _ = primePowerReduction p k T := congrArg (primePowerReduction p k) s.2.2.1
      _ = t := hT
  · have hunit := s.2.2.2.map (primePowerReduction p k)
    simpa [primePowerReduction_cubicDerivative] using hunit

/-- The fiber of reduction on distinguished solutions is exactly the
previously counted cubic solution-lift fiber. -/
noncomputable def distinguishedReductionFiberEquiv
    {p k n : ℕ} [NeZero p] (hk : 1 ≤ k)
    {t : ZMod (p ^ k)} (T : ZMod (p ^ (k + 1)))
    (hT : primePowerReduction p k T = t) (j : Fin n)
    (s : DistinguishedUnitSolution (p ^ k) n t j) :
    {z : DistinguishedUnitSolution (p ^ (k + 1)) n T j //
      reduceDistinguishedUnitSolution T hT j z = s} ≃
      CubicSolutionLiftFiber p k n s.1 T where
  toFun z := by
    have hpoint :
        (reduceDistinguishedUnitSolution T hT j z.1).1 = s.1 :=
      congrArg Subtype.val z.2
    exact ⟨⟨z.1.1, fun i ↦ congrFun hpoint i⟩, z.1.2.2.1⟩
  invFun z := by
    have hunit (i : Fin n) : IsUnit (z.1.1 i) := by
      apply isUnit_of_primePowerReduction_isUnit p k hk
      rw [z.1.2 i]
      exact s.2.1 i
    have hderivative : IsUnit (cubicDerivative (z.1.1 j)) := by
      apply isUnit_of_primePowerReduction_isUnit p k hk
      rw [primePowerReduction_cubicDerivative, z.1.2 j]
      exact s.2.2.2
    let lifted : DistinguishedUnitSolution (p ^ (k + 1)) n T j :=
      ⟨z.1.1, hunit, z.2, hderivative⟩
    refine ⟨lifted, ?_⟩
    apply Subtype.ext
    funext i
    exact z.1.2 i
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Decompose all next-level distinguished solutions into their reduced
base solution and their exact lift fiber. -/
noncomputable def distinguishedSolutionLiftSigmaEquiv
    {p k n : ℕ} [NeZero p] (hk : 1 ≤ k)
    {t : ZMod (p ^ k)} (T : ZMod (p ^ (k + 1)))
    (hT : primePowerReduction p k T = t) (j : Fin n) :
    DistinguishedUnitSolution (p ^ (k + 1)) n T j ≃
      Σ s : DistinguishedUnitSolution (p ^ k) n t j,
        CubicSolutionLiftFiber p k n s.1 T :=
  (Equiv.sigmaFiberEquiv
    (reduceDistinguishedUnitSolution T hT j)).symm.trans
      (Equiv.sigmaCongrRight fun s ↦
        distinguishedReductionFiberEquiv hk T hT j s)

/-- Exact one-step recurrence for the number of solutions having a fixed
unit derivative coordinate. -/
theorem card_distinguishedUnitSolution_lift_step
    {p k n : ℕ} [NeZero p] (hp : p.Prime) (hk : 1 ≤ k)
    {t : ZMod (p ^ k)} (T : ZMod (p ^ (k + 1)))
    (hT : primePowerReduction p k T = t) (j : Fin n) :
    Fintype.card (DistinguishedUnitSolution (p ^ (k + 1)) n T j) =
      Fintype.card (DistinguishedUnitSolution (p ^ k) n t j) *
        p ^ (n - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [Fintype.card_congr
    (distinguishedSolutionLiftSigmaEquiv hk T hT j), Fintype.card_sigma]
  simp_rw [show ∀ s : DistinguishedUnitSolution (p ^ k) n t j,
      Fintype.card (CubicSolutionLiftFiber p k n s.1 T) = p ^ (n - 1) by
    intro s
    exact card_nonsingularUnitSolution_lift_fiber hp hk
      (distinguishedToNonsingular
        (one_lt_pow₀ hp.one_lt (by omega)) s) j s.2.2.2 T hT]
  simp

/-- Iterating the recurrence from any distinguished solution modulo `p`
produces at least `p^((n-1)(k-1))` distinguished solutions modulo `p^k`. -/
theorem card_distinguishedUnitSolution_primePower_lower_bound
    {p n : ℕ} [NeZero p] (hp : p.Prime) (T : ℕ) (j : Fin n)
    (hbase : Nonempty
      (DistinguishedUnitSolution p n (T : ZMod p) j))
    (k : ℕ) (hk : 1 ≤ k) :
    p ^ ((n - 1) * (k - 1)) ≤
      Fintype.card
        (DistinguishedUnitSolution (p ^ k) n (T : ZMod (p ^ k)) j) := by
  induction k, hk using Nat.le_induction with
  | base =>
      have hbase' : Nonempty
          (DistinguishedUnitSolution (p ^ 1) n
            (T : ZMod (p ^ 1)) j) := by
        let family : ℕ → Prop := fun q ↦
          Nonempty (DistinguishedUnitSolution q n (T : ZMod q) j)
        exact Eq.mp (congrArg family (pow_one p).symm) hbase
      have hpositive : 0 < Fintype.card
          (DistinguishedUnitSolution (p ^ 1) n
            (T : ZMod (p ^ 1)) j) :=
        Fintype.card_pos_iff.mpr hbase'
      have hone : p ^ ((n - 1) * (1 - 1)) = 1 := by norm_num
      rw [hone]
      exact Nat.succ_le_iff.mpr hpositive
  | succ k hk ih =>
      have htarget : primePowerReduction p k
          (T : ZMod (p ^ (k + 1))) = (T : ZMod (p ^ k)) :=
        map_natCast (primePowerReduction p k) T
      rw [card_distinguishedUnitSolution_lift_step hp hk
        (T : ZMod (p ^ (k + 1))) htarget j]
      have hexponent : (n - 1) * (k + 1 - 1) =
          (n - 1) * (k - 1) + (n - 1) := by
        calc
          (n - 1) * (k + 1 - 1) = (n - 1) * k := by
            rw [Nat.succ_sub_one]
          _ = (n - 1) * ((k - 1) + 1) := by
            rw [Nat.sub_add_cancel hk]
          _ = (n - 1) * (k - 1) + (n - 1) := by
            rw [Nat.mul_add, Nat.mul_one]
      calc
        p ^ ((n - 1) * (k + 1 - 1)) =
            p ^ ((n - 1) * (k - 1)) * p ^ (n - 1) := by
          rw [hexponent, pow_add]
        _ ≤ Fintype.card
              (DistinguishedUnitSolution (p ^ k) n
                (T : ZMod (p ^ k)) j) * p ^ (n - 1) :=
          Nat.mul_le_mul_right _ ih

/-- Large-prime local solubility supplies a distinguished base solution. -/
theorem distinguishedUnitSolution_prime_exists
    {p n : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n)
    (T : ℕ) :
    ∃ j : Fin n,
      Nonempty (DistinguishedUnitSolution p n (T : ZMod p) j) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases nonsingularUnitSolution_exists hp hp5 hn5 (T : ZMod p) with ⟨s⟩
  rcases s.nonsingular with ⟨j, hj⟩
  refine ⟨j, ⟨⟨s.point, s.isUnit_point, s.equation, ?_⟩⟩⟩
  exact isUnit_iff_ne_zero.mpr hj

/-- A subtype presentation of the unit tuples counted by
`unitCubicSolutionCount`. -/
abbrev UnitCubicSolutionTuple (q n : ℕ) (T : ZMod q) :=
  {x : Fin n → (ZMod q)ˣ //
    CookMagyarFiniteFourier.unitCubicSum x = T}

/-- The filter-based finite count is the cardinality of its solution
subtype. -/
theorem unitCubicSolutionCount_eq_card_solutionTuple
    {q n : ℕ} [NeZero q] (T : ZMod q) :
    CookMagyarFiniteFourier.unitCubicSolutionCount n T =
      Fintype.card (UnitCubicSolutionTuple q n T) := by
  classical
  unfold CookMagyarFiniteFourier.unitCubicSolutionCount
  rw [Fintype.card_subtype]

/-- Forget the distinguished derivative while packaging every coordinate
as a unit. -/
noncomputable def distinguishedToUnitCubicSolutionTuple
    {q n : ℕ} [NeZero q] {T : ZMod q} {j : Fin n}
    (s : DistinguishedUnitSolution q n T j) :
    UnitCubicSolutionTuple q n T := by
  let units : Fin n → (ZMod q)ˣ := fun i ↦ (s.2.1 i).unit
  refine ⟨units, ?_⟩
  calc
    CookMagyarFiniteFourier.unitCubicSum units =
        ∑ i, cubicResidue (s.1 i) := by
      unfold CookMagyarFiniteFourier.unitCubicSum
      apply Finset.sum_congr rfl
      intro i _hi
      rw [(s.2.1 i).unit_spec]
      rfl
    _ = T := s.2.2.1

theorem distinguishedToUnitCubicSolutionTuple_injective
    {q n : ℕ} [NeZero q] {T : ZMod q} {j : Fin n} :
    Function.Injective
      (distinguishedToUnitCubicSolutionTuple
        (q := q) (n := n) (T := T) (j := j)) := by
  intro s t hst
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : UnitCubicSolutionTuple q n T ↦
    ((z.1 i : (ZMod q)ˣ) : ZMod q)) hst
  simpa [distinguishedToUnitCubicSolutionTuple] using hi

/-- Distinguished solutions form a subset of all unit solutions counted by
the finite Fourier count. -/
theorem card_distinguishedUnitSolution_le_unitCubicSolutionCount
    {q n : ℕ} [NeZero q] (T : ZMod q) (j : Fin n) :
    Fintype.card (DistinguishedUnitSolution q n T j) ≤
      CookMagyarFiniteFourier.unitCubicSolutionCount n T := by
  rw [unitCubicSolutionCount_eq_card_solutionTuple]
  exact Fintype.card_le_of_injective
    distinguishedToUnitCubicSolutionTuple
    distinguishedToUnitCubicSolutionTuple_injective

/-- Quantitative prime-power count obtained by iterating all nonsingular
lifts of one large-prime base solution. -/
theorem unitCubicSolutionCount_primePower_ge_lift_count
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n)
    (T k : ℕ) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    p ^ ((n - 1) * (k - 1)) ≤
      CookMagyarFiniteFourier.unitCubicSolutionCount n
        (T : ZMod (p ^ k)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases distinguishedUnitSolution_prime_exists hp hp5 hn5 T with
    ⟨j, hbase⟩
  calc
    p ^ ((n - 1) * (k - 1)) ≤
        Fintype.card
          (DistinguishedUnitSolution (p ^ k) n (T : ZMod (p ^ k)) j) :=
      card_distinguishedUnitSolution_primePower_lower_bound
        hp T j hbase k hk
    _ ≤ CookMagyarFiniteFourier.unitCubicSolutionCount n
          (T : ZMod (p ^ k)) :=
      card_distinguishedUnitSolution_le_unitCubicSolutionCount _ j

/-! ## A uniform normalized lower bound -/

/-- The normalization of the iterated lift count simplifies to a constant
independent of the prime-power exponent. -/
theorem primePower_lift_normalization_eq
    {p n k : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (p ^ k : ℝ) * (p ^ ((n - 1) * (k - 1)) : ℝ) /
        (Nat.totient (p ^ k) : ℝ) ^ n =
      (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n := by
  have hexponent : k + (n - 1) * (k - 1) = (k - 1) * n + 1 := by
    calc
      k + (n - 1) * (k - 1) =
          ((k - 1) + 1) + (n - 1) * (k - 1) := by
        rw [Nat.sub_add_cancel hk]
      _ = ((n - 1) + 1) * (k - 1) + 1 := by ring
      _ = n * (k - 1) + 1 := by rw [Nat.sub_add_cancel hn]
      _ = (k - 1) * n + 1 := by rw [Nat.mul_comm]
  rw [Nat.totient_prime_pow hp (by omega)]
  simp only [Nat.cast_pow, Nat.cast_mul]
  rw [← pow_add, hexponent, pow_add, pow_one, mul_pow, ← pow_mul]
  have hp_real : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcommon : (p : ℝ) ^ ((k - 1) * n) ≠ 0 :=
    pow_ne_zero _ hp_real
  exact mul_div_mul_left _ _ hcommon

/-- **Uniform large-prime local lower bound.**  For every positive
prime-power level, the normalized unit count is bounded below by
`p/(p-1)^n`, independently of `k`. -/
theorem normalizedUnitCubicCount_primePower_uniform_lower_bound
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n)
    (T k : ℕ) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n ≤
      CookMagyarFiniteFourier.normalizedUnitCubicCount n
        (T : ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcount := unitCubicSolutionCount_primePower_ge_lift_count
    hp hp5 hn5 T k hk
  have hcount_real : (p ^ ((n - 1) * (k - 1)) : ℝ) ≤
      CookMagyarFiniteFourier.unitCubicSolutionCount n
        (T : ZMod (p ^ k)) := by
    exact_mod_cast hcount
  have htotient : 0 < (Nat.totient (p ^ k) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have hdenominator : 0 < (Nat.totient (p ^ k) : ℝ) ^ n :=
    pow_pos htotient n
  rw [← primePower_lift_normalization_eq hp (by omega) hk]
  unfold CookMagyarFiniteFourier.normalizedUnitCubicCount
  simp only [Nat.cast_pow]
  apply (div_le_div_iff_of_pos_right hdenominator).2
  exact mul_le_mul_of_nonneg_left hcount_real
    (pow_nonneg (Nat.cast_nonneg p) k)

end CookMagyarLocal
end SystolicGrowth
