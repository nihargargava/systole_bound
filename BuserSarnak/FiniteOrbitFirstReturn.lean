module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# First return to a nonempty subset of a finite transitive orbit

This is the finite-set part of the Buser--Sarnak elimination argument. It
proves that first return to any nonempty subset preserves a single orbit;
the contour-specific splice still has to be shown to realize this return map.
-/

namespace SystolicGrowth

noncomputable section

/-- On a finite type, injectivity gives every point a positive return time.
Combining this with transitivity gives a positive hit on any nonempty subset. -/
theorem finiteOrbit_exists_positive_hit
    {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Injective f)
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y)
    (P : X → Prop) (hP : ∃ x, P x) (x : X) :
    ∃ n : ℕ, 0 < n ∧ P (f^[n] x) := by
  obtain ⟨y, hy⟩ := hP
  obtain ⟨n, hn⟩ := horbit x y
  by_cases hn0 : n = 0
  · subst n
    have hxy : x = y := by simpa using hn
    subst y
    obtain ⟨m, hmpos, hm⟩ :=
      (Function.mem_periodicPts).mp (hf.mem_periodicPts x)
    change f^[m] x = x at hm
    exact ⟨m, hmpos, by rw [hm]; exact hy⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    exact ⟨n, hnpos, by simpa [hn] using hy⟩

/-- The least positive time at which the orbit of `x` next meets `P`. -/
noncomputable def finiteOrbitFirstReturnTime
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) : ℕ :=
  Nat.find (hreturn x)

/-- The first-return map on the subtype of points in `P`. -/
noncomputable def finiteOrbitFirstReturn
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1)) :
    {x : X // P x} → {x : X // P x} := fun x =>
  ⟨f^[finiteOrbitFirstReturnTime f P hreturn x] x.1,
    (Nat.find_spec (hreturn x)).2⟩

theorem finiteOrbitFirstReturnTime_pos
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) :
    0 < finiteOrbitFirstReturnTime f P hreturn x :=
  (Nat.find_spec (hreturn x)).1

theorem finiteOrbitFirstReturnTime_hit
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) :
    P (f^[finiteOrbitFirstReturnTime f P hreturn x] x.1) :=
  (Nat.find_spec (hreturn x)).2

/-- A pointwise intertwining equivalence transports one-orbit dynamics. -/
theorem one_orbit_of_conjugate
    {X Y : Type*} (f : X → X) (g : Y → Y) (e : X ≃ Y)
    (hcommute : ∀ x, e (f x) = g (e x))
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y) :
    ∀ x y : Y, ∃ n : ℕ, g^[n] x = y := by
  have hiterate : ∀ n x, e (f^[n] x) = g^[n] (e x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hcommute, ih]
  intro x y
  obtain ⟨n, hn⟩ := horbit (e.symm x) (e.symm y)
  refine ⟨n, ?_⟩
  calc
    g^[n] x = e (f^[n] (e.symm x)) := by
      rw [hiterate, e.apply_symm_apply]
    _ = e (e.symm y) := congrArg e hn
    _ = y := e.apply_symm_apply y

/-- A transitive self-map of a finite type is a permutation: every point has
a predecessor. For a chosen base point, use a distinct point and a positive
orbit path when one exists; the singleton case is immediate. -/
theorem finite_one_orbit_injective
    {X : Type*} [Finite X] (f : X → X)
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y) :
    Function.Injective f := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    have hsurj : Function.Surjective f := by
      intro y
      by_cases hy : y = x₀
      · by_cases hsingleton : ∀ z, z = x₀
        · refine ⟨x₀, ?_⟩
          exact (hsingleton (f x₀)).trans hy.symm
        · obtain ⟨z, hz⟩ : ∃ z, z ≠ x₀ := by
            by_contra hnot
            apply hsingleton
            intro z
            by_contra hz
            exact hnot ⟨z, hz⟩
          obtain ⟨n, hn⟩ := horbit z x₀
          have hn0 : n ≠ 0 := by
            intro hn0
            subst n
            exact hz (by simpa using hn)
          refine ⟨f^[n - 1] z, ?_⟩
          rw [← Function.iterate_succ_apply' f (n - 1) z]
          have hpred : Nat.succ (n - 1) = n := by omega
          rw [hpred]
          simpa [hy] using hn
      · obtain ⟨n, hn⟩ := horbit x₀ y
        have hn0 : n ≠ 0 := by
          intro hn0
          subst n
          exact hy (by simpa using hn.symm)
        refine ⟨f^[n - 1] x₀, ?_⟩
        rw [← Function.iterate_succ_apply' f (n - 1) x₀]
        have hpred : Nat.succ (n - 1) = n := by omega
        rw [hpred]
        exact hn
    exact (Finite.injective_iff_surjective).2 hsurj
  · intro x y hxy
    exact isEmptyElim (hX ⟨x⟩)

@[simp] theorem finiteOrbitFirstReturn_val
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) :
    (finiteOrbitFirstReturn f P hreturn x).1 =
      f^[finiteOrbitFirstReturnTime f P hreturn x] x.1 := rfl

/-- If the original finite permutation is transitive, its induced first-return
map on a nonempty subset is transitive too. This is the orbit-preservation
half of the contour contraction bridge. -/
theorem finiteOrbitFirstReturn_one_orbit
    {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Injective f)
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y)
    (P : X → Prop) [DecidablePred P] (hP : ∃ x, P x) :
    let hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1) :=
      fun x => finiteOrbit_exists_positive_hit f hf horbit P hP x.1
    ∀ x y : {x : X // P x},
      ∃ k : ℕ,
        (finiteOrbitFirstReturn f P hreturn)^[k] x = y := by
  dsimp only
  let hreturn : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1) :=
    fun x => finiteOrbit_exists_positive_hit f hf horbit P hP x.1
  let r : {x : X // P x} → {x : X // P x} :=
    finiteOrbitFirstReturn f P hreturn
  have hhit : ∀ (n : ℕ) (x : {x : X // P x})
      (hxn : P (f^[n] x.1)),
      ∃ k : ℕ, r^[k] x = ⟨f^[n] x.1, hxn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hxn
      by_cases hn0 : n = 0
      · subst n
        refine ⟨0, ?_⟩
        apply Subtype.ext
        rfl
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let t := finiteOrbitFirstReturnTime f P hreturn x
        have htpos : 0 < t := by
          exact finiteOrbitFirstReturnTime_pos f P hreturn x
        have hthit : P (f^[t] x.1) := by
          simpa [t] using finiteOrbitFirstReturnTime_hit f P hreturn x
        have htle : t ≤ n := by
          apply Nat.find_min' (hreturn x)
          exact ⟨hnpos, hxn⟩
        by_cases hteq : t = n
        · have htime : finiteOrbitFirstReturnTime f P hreturn x = n := by
            simpa [t] using hteq
          subst t
          have hreturn_eq : r x = ⟨f^[n] x.1, hxn⟩ := by
            apply Subtype.ext
            change f^[finiteOrbitFirstReturnTime f P hreturn x] x.1 =
              f^[n] x.1
            rw [htime]
          exact ⟨1, by simpa [r, Function.iterate_succ_apply] using hreturn_eq⟩
        · have htlt : t < n := lt_of_le_of_ne htle hteq
          let x' := r x
          have hiter : f^[n - t] x'.1 = f^[n] x.1 := by
            change f^[n - t] (f^[t] x.1) = f^[n] x.1
            rw [← Function.iterate_add_apply]
            rw [Nat.sub_add_cancel (le_of_lt htlt)]
          have hsmall : n - t < n := Nat.sub_lt hnpos htpos
          have hsmallhit : P (f^[n - t] x'.1) := by
            rw [hiter]
            exact hxn
          obtain ⟨k, hk⟩ := ih (n - t) hsmall x' hsmallhit
          have htarget :
              (⟨f^[n - t] x'.1, hsmallhit⟩ : {x : X // P x}) =
                ⟨f^[n] x.1, hxn⟩ := by
            apply Subtype.ext
            exact hiter
          refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          change r^[k] x' = ⟨f^[n] x.1, hxn⟩
          exact hk.trans htarget
  intro x y
  obtain ⟨n, hn⟩ := horbit x.1 y.1
  have hxn : P (f^[n] x.1) := by simpa [hn] using y.2
  obtain ⟨k, hk⟩ := hhit n x hxn
  exact ⟨k, hk.trans (Subtype.ext hn)⟩

/-- First-return restrictions can be iterated. After restricting a finite
transitive orbit to `P`, the induced map is again a finite transitive orbit;
restricting that return map to any nonempty `Q` therefore remains transitive.
This is the abstract compositional step for a sequence of occurrence
deletions. -/
theorem finiteOrbitFirstReturn_nested_one_orbit
    {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Injective f)
    (horbit : ∀ x y : X, ∃ n : ℕ, f^[n] x = y)
    (P : X → Prop) [DecidablePred P] (hP : ∃ x, P x)
    (Q : {x : X // P x} → Prop) [DecidablePred Q]
    (hQ : ∃ x, Q x) :
    let hreturnP : ∀ x : {x : X // P x},
        ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1) :=
      fun x => finiteOrbit_exists_positive_hit f hf horbit P hP x.1
    let rP : {x : X // P x} → {x : X // P x} :=
      finiteOrbitFirstReturn f P hreturnP
    let horbitP : ∀ x y : {x : X // P x}, ∃ n : ℕ, rP^[n] x = y :=
      finiteOrbitFirstReturn_one_orbit f hf horbit P hP
    let hreturnQ : ∀ x : {x : {x : X // P x} // Q x},
        ∃ n : ℕ, 0 < n ∧ Q (rP^[n] x.1) :=
      fun x => finiteOrbit_exists_positive_hit rP
        (finite_one_orbit_injective rP horbitP) horbitP Q hQ x.1
    ∀ x y : {x : {x : X // P x} // Q x},
      ∃ k : ℕ, (finiteOrbitFirstReturn rP Q hreturnQ)^[k] x = y := by
  dsimp only
  let hreturnP : ∀ x : {x : X // P x},
      ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1) :=
    fun x => finiteOrbit_exists_positive_hit f hf horbit P hP x.1
  let rP : {x : X // P x} → {x : X // P x} :=
    finiteOrbitFirstReturn f P hreturnP
  have horbitP : ∀ x y : {x : X // P x}, ∃ n : ℕ, rP^[n] x = y := by
    simpa [rP, hreturnP] using
      (finiteOrbitFirstReturn_one_orbit f hf horbit P hP)
  have hrP : Function.Injective rP := finite_one_orbit_injective rP horbitP
  let hreturnQ : ∀ x : {x : {x : X // P x} // Q x},
      ∃ n : ℕ, 0 < n ∧ Q (rP^[n] x.1) :=
    fun x => finiteOrbit_exists_positive_hit rP hrP horbitP Q hQ x.1
  exact finiteOrbitFirstReturn_one_orbit rP hrP horbitP Q hQ

#print axioms one_orbit_of_conjugate
#print axioms finite_one_orbit_injective
#print axioms finiteOrbitFirstReturn_one_orbit
#print axioms finiteOrbitFirstReturn_nested_one_orbit

end

end SystolicGrowth
