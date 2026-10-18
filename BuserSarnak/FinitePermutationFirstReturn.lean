module

public import BuserSarnak.FiniteOrbitFirstReturn
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-!
# First return for finite permutations

A retained point of any finite permutation has a positive return to the
retained set, by periodicity. Thus the return map itself needs neither
transitivity nor a separately supplied nonemptiness witness. Transitivity
of the ambient permutation implies transitivity of this return map.
-/

namespace SystolicGrowth

noncomputable section

/-- Periodicity supplies a positive retained hit for every retained point. -/
theorem finitePermutation_exists_positive_return
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    (x : {x : X // P x}) : ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1) := by
  obtain ⟨n, hn, hperiod⟩ :=
    (Function.mem_periodicPts).mp (f.injective.mem_periodicPts x.1)
  change f^[n] x.1 = x.1 at hperiod
  exact ⟨n, hn, by rw [hperiod]; exact x.2⟩

/-- The first-return map is defined even when the retained set is empty. -/
def finitePermutationFirstReturn
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] : {x : X // P x} → {x : X // P x} :=
  finiteOrbitFirstReturn f P (finitePermutation_exists_positive_return f P)

/-- The least positive retained hit of a finite permutation. -/
def finitePermutationFirstReturnTime
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] (x : {x : X // P x}) : ℕ :=
  finiteOrbitFirstReturnTime f P (finitePermutation_exists_positive_return f P) x

@[simp] theorem finitePermutationFirstReturn_val
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] (x : {x : X // P x}) :
    (finitePermutationFirstReturn f P x).1 =
      f^[finitePermutationFirstReturnTime f P x] x.1 := rfl

theorem finitePermutationFirstReturnTime_pos
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] (x : {x : X // P x}) :
    0 < finitePermutationFirstReturnTime f P x :=
  finiteOrbitFirstReturnTime_pos f P _ x

/-- No earlier positive iterate is retained. -/
theorem finitePermutationFirstReturnTime_min
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] (x : {x : X // P x}) {n : ℕ}
    (hn : 0 < n) (hlt : n < finitePermutationFirstReturnTime f P x) :
    ¬ P (f^[n] x.1) := by
  intro hhit
  exact Nat.find_min (finitePermutation_exists_positive_return f P x) hlt ⟨hn, hhit⟩

/-- When the next ambient point is retained, it is already the first return. -/
theorem finitePermutationFirstReturn_val_eq_of_mem_apply
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P] (x : {x : X // P x}) (hhit : P (f x.1)) :
    (finitePermutationFirstReturn f P x).1 = f x.1 := by
  have hle : finitePermutationFirstReturnTime f P x ≤ 1 :=
    Nat.find_min' (finitePermutation_exists_positive_return f P x)
      ⟨by omega, by simpa using hhit⟩
  have htime : finitePermutationFirstReturnTime f P x = 1 := by
    have hpos := finitePermutationFirstReturnTime_pos f P x
    omega
  rw [finitePermutationFirstReturn_val, htime]
  rfl

/-- A single ambient orbit induces a single orbit on retained points. Empty
retained sets cause no extra hypothesis: the conclusion is then vacuous. -/
theorem finitePermutationFirstReturn_one_orbit
    {X : Type*} [Finite X] (f : Equiv.Perm X) (P : X → Prop)
    [DecidablePred P]
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y) :
    ∀ x y : {x : X // P x},
      ∃ n : ℕ, (finitePermutationFirstReturn f P)^[n] x = y := by
  intro x y
  exact finiteOrbitFirstReturn_one_orbit f f.injective horbit P ⟨x.1, x.2⟩ x y

#print axioms finitePermutation_exists_positive_return
#print axioms finitePermutationFirstReturnTime_min
#print axioms finitePermutationFirstReturn_val_eq_of_mem_apply
#print axioms finitePermutationFirstReturn_one_orbit

end

end SystolicGrowth
