module

public import BuserSarnak.FiniteFaceMerge

@[expose] public section

/-!
# Positive orbit gaps through omitted points

The relation records a positive orbit segment with no retained intermediate
point. It composes precisely when the middle endpoint is omitted, and a
retained final endpoint is the least positive hit. These are the local
interfaces for assembling open child tours into the literal root contour.
-/

namespace SystolicGrowth

/-- A positive orbit segment with no retained intermediate point. Neither
endpoint is required to be retained, so deleted pivots can be sentinels. -/
def PositiveOrbitGap {X : Type*} (f : X → X) (P : X → Prop) (x y : X) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f^[n] x = y ∧
    ∀ k : ℕ, 0 < k → k < n → ¬ P (f^[k] x)

theorem positiveOrbitGap_step {X : Type*} (f : X → X) (P : X → Prop) (x : X) :
    PositiveOrbitGap f P x (f x) := by
  refine ⟨1, by omega, rfl, ?_⟩
  intro k hk hlt
  omega

/-- Orbit gaps concatenate only if their common endpoint is omitted. -/
theorem PositiveOrbitGap.trans_of_not_mem
    {X : Type*} {f : X → X} {P : X → Prop} {x y z : X}
    (hxy : PositiveOrbitGap f P x y) (hyz : PositiveOrbitGap f P y z)
    (hy : ¬ P y) : PositiveOrbitGap f P x z := by
  obtain ⟨n, hn, hxy, hbefore⟩ := hxy
  obtain ⟨m, hm, hyz, hafter⟩ := hyz
  refine ⟨n + m, by omega, ?_, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, hxy, hyz]
  · intro k hk hkm
    by_cases hkn : k < n
    · exact hbefore k hk hkn
    · by_cases hkeq : k = n
      · subst k
        simpa only [hxy] using hy
      · have hnk : n ≤ k := Nat.le_of_not_gt hkn
        have hpositive : 0 < k - n := by omega
        have hsmall : k - n < m := by omega
        have hiterate : f^[k] x = f^[k - n] y := by
          conv_lhs => rw [← Nat.sub_add_cancel hnk]
          rw [Function.iterate_add_apply, hxy]
        rw [hiterate]
        exact hafter (k - n) hpositive hsmall

/-- A retained endpoint of an omitted-only positive segment is exactly
first return, not merely some later retained orbit point. -/
theorem PositiveOrbitGap.firstReturn_val_eq
    {X : Type*} {f : X → X} {P : X → Prop} [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) {y : X}
    (hgap : PositiveOrbitGap f P x.1 y) (hy : P y) :
    (finiteOrbitFirstReturn f P hreturn x).1 = y := by
  obtain ⟨n, hn, hendpoint, hbefore⟩ := hgap
  rw [finiteOrbitFirstReturn_val_eq_of_first_hit f P hreturn x n hn
    (by rw [hendpoint]; exact hy) hbefore]
  exact hendpoint

#print axioms PositiveOrbitGap.trans_of_not_mem
#print axioms PositiveOrbitGap.firstReturn_val_eq

end SystolicGrowth
