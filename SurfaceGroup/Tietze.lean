module

public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze

@[expose] public section

namespace SystolicGrowth

open ReidemeisterSchreier.Discrete.Presentations

variable {G : Type*} [Group G]

/-- The ordered product `W_0 ... W_(n-1)` occurring in a cyclic-cover
Schreier presentation. -/
def cyclicPrefixProduct (W : ℕ → G) (n : ℕ) : G :=
  ((List.range n).map W).prod

/-- The word forced for `B_n` by the relations
`B_(j+1) B_j^-1 W_j = 1`. -/
def cyclicRecurrenceNormalForm (B0 : G) (W : ℕ → G) (n : ℕ) : G :=
  (cyclicPrefixProduct W n)⁻¹ * B0

@[simp] lemma cyclicPrefixProduct_zero (W : ℕ → G) :
    cyclicPrefixProduct W 0 = 1 := by
  simp [cyclicPrefixProduct]

lemma cyclicPrefixProduct_succ (W : ℕ → G) (n : ℕ) :
    cyclicPrefixProduct W (n + 1) = cyclicPrefixProduct W n * W n := by
  simp [cyclicPrefixProduct, List.range_succ, List.map_append]

@[simp] lemma cyclicRecurrenceNormalForm_zero (B0 : G) (W : ℕ → G) :
    cyclicRecurrenceNormalForm B0 W 0 = B0 := by
  simp [cyclicRecurrenceNormalForm]

lemma cyclicRecurrenceNormalForm_succ (B0 : G) (W : ℕ → G) (n : ℕ) :
    cyclicRecurrenceNormalForm B0 W (n + 1) =
      (W n)⁻¹ * cyclicRecurrenceNormalForm B0 W n := by
  rw [cyclicRecurrenceNormalForm, cyclicPrefixProduct_succ,
    cyclicRecurrenceNormalForm]
  group

/-- Solving a Schreier step relation for its new generator is valid modulo the
normal closure of the relators. -/
lemma relatorEquivalent_eq_inv_mul_of_mul_inv_mul_eq_one {R : Set G} {A B W : G}
    (h : RelatorEquivalent R (A * B⁻¹ * W) 1) :
    RelatorEquivalent R A (W⁻¹ * B) := by
  rw [relatorEquivalent_iff_eq_in_presentedQuotient] at h ⊢
  change ((A * B⁻¹ * W : G) : G ⧸ Subgroup.normalClosure R) = 1 at h
  calc
    (A : G ⧸ Subgroup.normalClosure R) =
        (A * B⁻¹ * W : G) * (W⁻¹ * B : G) := by
          change (A : G ⧸ Subgroup.normalClosure R) =
            ((A : G ⧸ Subgroup.normalClosure R) *
              (B : G ⧸ Subgroup.normalClosure R)⁻¹ *
              (W : G ⧸ Subgroup.normalClosure R)) *
              ((W : G ⧸ Subgroup.normalClosure R)⁻¹ *
                (B : G ⧸ Subgroup.normalClosure R))
          group
    _ = (1 : G ⧸ Subgroup.normalClosure R) * (W⁻¹ * B : G) := by rw [h]
    _ = (W⁻¹ * B : G) := by simp

/-- All sheet generators satisfy their closed recursive normal forms modulo
the Schreier step relators. -/
theorem cyclicRecurrence_relatorEquivalent
    {R : Set G} (B : ℕ → G) (W : ℕ → G)
    (hstep : ∀ n, RelatorEquivalent R (B (n + 1) * (B n)⁻¹ * W n) 1) :
    ∀ n, RelatorEquivalent R (B n) (cyclicRecurrenceNormalForm (B 0) W n) := by
  intro n
  induction n with
  | zero => simp only [cyclicRecurrenceNormalForm_zero]; exact RelatorEquivalent.refl R (B 0)
  | succ n ih =>
      refine (relatorEquivalent_eq_inv_mul_of_mul_inv_mul_eq_one (hstep n)).trans ?_
      rw [cyclicRecurrenceNormalForm_succ]
      exact RelatorEquivalent.mul (RelatorEquivalent.refl R (W n)⁻¹) ih

/-- Bounded form of `cyclicRecurrence_relatorEquivalent`, suited to a finite
Schreier transversal. -/
theorem cyclicRecurrence_relatorEquivalent_of_lt
    {R : Set G} (B : ℕ → G) (W : ℕ → G) (bound : ℕ)
    (hstep : ∀ n, n < bound →
      RelatorEquivalent R (B (n + 1) * (B n)⁻¹ * W n) 1) :
    ∀ n, n ≤ bound →
      RelatorEquivalent R (B n) (cyclicRecurrenceNormalForm (B 0) W n) := by
  intro n hn
  induction n with
  | zero =>
      simp only [cyclicRecurrenceNormalForm_zero]
      exact RelatorEquivalent.refl R (B 0)
  | succ n ih =>
      have hnlt : n < bound := Nat.lt_of_succ_le hn
      refine (relatorEquivalent_eq_inv_mul_of_mul_inv_mul_eq_one
        (hstep n hnlt)).trans ?_
      rw [cyclicRecurrenceNormalForm_succ]
      exact RelatorEquivalent.mul (RelatorEquivalent.refl R (W n)⁻¹)
        (ih (Nat.le_of_lt hnlt))

/-- After eliminating the recursively defined `B_j`, the wraparound relator is
the standard surface relator `[A,B_0] W_0 ... W_n`. -/
theorem cyclicFinalRelator_relatorEquivalent
    {R : Set G} (A : G) (B : ℕ → G) (W : ℕ → G) (n : ℕ)
    (hstep : ∀ j, RelatorEquivalent R (B (j + 1) * (B j)⁻¹ * W j) 1)
    (hfinal : RelatorEquivalent R (A * B 0 * A⁻¹ * (B n)⁻¹ * W n) 1) :
    RelatorEquivalent R
      (A * B 0 * A⁻¹ * (B 0)⁻¹ * cyclicPrefixProduct W (n + 1)) 1 := by
  have hB := cyclicRecurrence_relatorEquivalent B W hstep n
  have hBinv := RelatorEquivalent.inv hB
  have hreplace : RelatorEquivalent R
      (A * B 0 * A⁻¹ * (B n)⁻¹ * W n)
      (A * B 0 * A⁻¹ *
        (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n) := by
    exact RelatorEquivalent.mul
      (RelatorEquivalent.mul
        (RelatorEquivalent.refl R (A * B 0 * A⁻¹)) hBinv)
      (RelatorEquivalent.refl R (W n))
  have hright : RelatorEquivalent R
      (A * B 0 * A⁻¹ *
        (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n) 1 :=
    hreplace.symm.trans hfinal
  have heq :
      A * B 0 * A⁻¹ * (B 0)⁻¹ * cyclicPrefixProduct W (n + 1) =
        A * B 0 * A⁻¹ *
          (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n := by
    rw [cyclicRecurrenceNormalForm, cyclicPrefixProduct_succ]
    group
  exact (RelatorEquivalent.of_eq heq).trans hright

/-- Finite version of `cyclicFinalRelator_relatorEquivalent`: only the steps
strictly before the final sheet are required. -/
theorem cyclicFinalRelator_relatorEquivalent_of_lt
    {R : Set G} (A : G) (B : ℕ → G) (W : ℕ → G) (n : ℕ)
    (hstep : ∀ j, j < n →
      RelatorEquivalent R (B (j + 1) * (B j)⁻¹ * W j) 1)
    (hfinal : RelatorEquivalent R (A * B 0 * A⁻¹ * (B n)⁻¹ * W n) 1) :
    RelatorEquivalent R
      (A * B 0 * A⁻¹ * (B 0)⁻¹ * cyclicPrefixProduct W (n + 1)) 1 := by
  have hB := cyclicRecurrence_relatorEquivalent_of_lt B W n hstep n le_rfl
  have hBinv := RelatorEquivalent.inv hB
  have hreplace : RelatorEquivalent R
      (A * B 0 * A⁻¹ * (B n)⁻¹ * W n)
      (A * B 0 * A⁻¹ *
        (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n) := by
    exact RelatorEquivalent.mul
      (RelatorEquivalent.mul
        (RelatorEquivalent.refl R (A * B 0 * A⁻¹)) hBinv)
      (RelatorEquivalent.refl R (W n))
  have hright : RelatorEquivalent R
      (A * B 0 * A⁻¹ *
        (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n) 1 :=
    hreplace.symm.trans hfinal
  have heq :
      A * B 0 * A⁻¹ * (B 0)⁻¹ * cyclicPrefixProduct W (n + 1) =
        A * B 0 * A⁻¹ *
          (cyclicRecurrenceNormalForm (B 0) W n)⁻¹ * W n := by
    rw [cyclicRecurrenceNormalForm, cyclicPrefixProduct_succ]
    group
  exact (RelatorEquivalent.of_eq heq).trans hright

end SystolicGrowth
